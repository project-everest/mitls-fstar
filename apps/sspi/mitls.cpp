//////////////////////////////////////////////////////////////////////////////
//
//  Implements an schannel-like API on top of miTLS
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
#define _WIN32_WINNT        _WIN32_WINNT_WINBLUE
#define NTDDI_VERSION       NTDDI_WINBLUE 
#define SECURITY_WIN32  // tell Sspi.h which feature set we consume
#define WINNT 1         // avoid conflict between ddraw.h and winerror.h

#include <windows.h>
#include <Sspi.h>
#include <schnlsp.h>
#include <queue>
#include "mitls.h"
extern "C" {
#include "..\..\libs\ffi\mitlsffi.h"
}

typedef int  (MITLS_CALLCONV *tFFI_mitls_init)(void);
typedef void (MITLS_CALLCONV *tFFI_mitls_cleanup)(void);
typedef int  (MITLS_CALLCONV *tFFI_mitls_configure)(/* out */ mitls_state **state, const char *tls_version, const char *host_name, /* out */ char **outmsg, /* out */ char **errmsg);
typedef void (MITLS_CALLCONV *tFFI_mitls_close)(/* in */ mitls_state *state);
typedef int  (MITLS_CALLCONV *tFFI_mitls_connect)(struct _FFI_mitls_callbacks *callbacks, /* in */ mitls_state *state, /* out */ char **outmsg, /* out */ char **errmsg);
typedef int (MITLS_CALLCONV *tFFI_mitls_send)(/* in */ mitls_state *state, const void* buffer, size_t buffer_size,
    /* out */ char **outmsg, /* out */ char **errmsg); // Returns NULL for failure, or a TCP packet to be sent then freed with FFI_mitls_free_packet()
typedef void *(MITLS_CALLCONV *tFFI_mitls_receive)(/* in */ mitls_state *state, /* out */ size_t *packet_size,
    /* out */ char **outmsg, /* out */ char **errmsg);     // Returns NULL for failure, a plaintext packet to be freed with FFI_mitls_free_packet()
typedef void (MITLS_CALLCONV *tFFI_mitls_free_packet)(void* packet);
typedef void (MITLS_CALLCONV *tFFI_mitls_free_msg)(char *msg);
typedef int (MITLS_CALLCONV *tFFI_mitls_thread_register)(void);
typedef int (MITLS_CALLCONV *tFFI_mitls_thread_unregister)(void);
typedef void *(MITLS_CALLCONV *tFFI_mitls_get_cert)(/* in */ mitls_state *state, /* out */ size_t *cert_size, /* out */ char **outmsg, /* out */ char **errmsg);

void MITLS_ProcessMessages(char *outmsg, char *errmsg);
int MITLS_CALLCONV MITLS_send_callback(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size);
int MITLS_CALLCONV MITLS_recv_callback(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size);

typedef enum _TLS_WORK_ITEM_TYPE {
    TLS_CONNECT,
    TLS_SEND,
    TLS_RECV,
    TLS_DISCONNECT,
    TLS_EXIT_THREAD
} TLS_WORK_ITEM_TYPE;

typedef struct _MitlsCredHandle {
    char TlsVersion[64];
} MITLS_CredHandle;

typedef struct _TLS_WORK_ITEM TLS_WORK_ITEM;

typedef struct _ConnectionState {
    // Each connection has an associated worker thread
    std::queue<TLS_WORK_ITEM*> mitlsQueue;
    CRITICAL_SECTION queueLock;
    HANDLE hqueueReady;
    HANDLE hWorkerThread;

    TLS_WORK_ITEM *item; // ptr to work item while InitializeSecurityContext is running, NULL afterwards.
    mitls_state *state;
    struct _FFI_mitls_callbacks callbacks;

    HANDLE hOutputIsReady;
    HANDLE hNextCallReady;

    // Arguments passed to InitializeSecurityContext
    MITLS_CredHandle *cred;
    PSecBufferDesc pInput;
    PSecBufferDesc pOutput;
    PSecBuffer pOutputBuffer;
    unsigned long fContextReq;
    SECURITY_STATUS status;

    // The pInput buffer to actually read from.  This is initially a copy of the
    // caller's SECBUFFER_TOKEN SecBuffer, but as it is incrementally read from,
    // the buffer pointer and length can change.
    SecBuffer ActualInputToken;

    bool fShuttingDownConnection;
    bool fDeleteOnComplete;

    BYTE *peer_cert;
    DWORD peer_cert_length;
} ConnectionState;

typedef struct _TLS_CONNECT_WORK_ITEM {
    const char *HostName;
    ConnectionState *state;     // bugbug: this can be leaked in some codepaths.
} TLS_CONNECT_WORK_ITEM;

typedef struct _TLS_SEND_WORK_ITEM {
    ConnectionState *state;
} TLS_SEND_WORK_ITEM;

typedef struct _TLS_RECV_WORK_ITEM {
    ConnectionState *state;
} TLS_RECV_WORK_ITEM;

typedef struct _TLS_DISCONNECT_WORK_ITEM {
    ConnectionState *state;
} TLS_DISCONNECT_WORK_ITEM;

typedef struct _TLS_WORK_ITEM {
    TLS_WORK_ITEM_TYPE Type;
    HANDLE hWorkItemCompleted; // bugbug: this is leaked.  This needs to be a class with a destructor

    union {
        TLS_CONNECT_WORK_ITEM Connect;
        TLS_SEND_WORK_ITEM Send;
        TLS_RECV_WORK_ITEM Recv;
        TLS_DISCONNECT_WORK_ITEM Disconnect;
    };

} TLS_WORK_ITEM;

tFFI_mitls_init pfnFFI_mitls_init;
tFFI_mitls_cleanup pfnFFI_mitls_cleanup;
tFFI_mitls_configure pfnFFI_mitls_configure;
tFFI_mitls_close pfnFFI_mitls_close;
tFFI_mitls_connect pfnFFI_mitls_connect;
tFFI_mitls_send pfnFFI_mitls_send;
tFFI_mitls_receive pfnFFI_mitls_receive;
tFFI_mitls_free_packet pfnFFI_mitls_free_packet;
tFFI_mitls_free_msg pfnFFI_mitls_free_msg;
tFFI_mitls_thread_register pfnFFI_mitls_thread_register;
tFFI_mitls_thread_unregister pfnFFI_mitls_thread_unregister;
tFFI_mitls_get_cert pfnFFI_mitls_get_cert;

const char *_formats[] = {
    "",
    " %2.2x",
    " %2.2x %2.2x",
    " %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x",
    " %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x %2.2x"
};
void _PrintBuffer(const void *buffer, size_t length)
{
    if (length > 10) {
        length = 10;
    }
    const unsigned char*b = (const unsigned char*)buffer;
    _Print(_formats[length], b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9]);
}

BOOL MITLS_IsMITLSHandle(PSecHandle h)
{
    if (h->dwLower != 0) {
        // schannel treats dwLower==0 or ==-1 as invalid
        return FALSE;
    }
    return TRUE;
}

void ProcessConnect(TLS_CONNECT_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    char *outmsg;
    char *errmsg;
    _Print("FFI_mitls_configure - TlsVersion=%s hostname=%s", state->cred->TlsVersion, item->HostName);
    int ret = pfnFFI_mitls_configure(&state->state, state->cred->TlsVersion, item->HostName, &outmsg, &errmsg);
    MITLS_ProcessMessages(outmsg, errmsg);
    if (ret == 0) {
        // Failed
        _Print("MITLS Configure failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }

    state->callbacks.send = MITLS_send_callback;
    state->callbacks.recv = MITLS_recv_callback;
    ret = pfnFFI_mitls_connect(&state->callbacks, state->state, &outmsg, &errmsg);
    MITLS_ProcessMessages(outmsg, errmsg);
    if (ret == 0) {
        // Failed
        _Print("MITLS Connect failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }
    _Print("FFI_mitls_get_cert");
    size_t cb;
    void *pb = pfnFFI_mitls_get_cert(state->state, &cb, &outmsg, &errmsg);
    MITLS_ProcessMessages(outmsg, errmsg);
    if (pb == NULL) {
        _Print("Failed to get the peer certificate");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }
    state->peer_cert = (BYTE*)pb;
    state->peer_cert_length = (DWORD)cb;
    state->status = SEC_E_OK;
    if (state->fDeleteOnComplete) {
        _Print("Deleting state per request, at the end of the miTLS connect");
        delete state;
        ExitThread(0);
    }
}

void ProcessSend(TLS_SEND_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    // Although the SChannel docs for EncryptMessage() state that the buffers must be exactly:
    //  SECBUFFER_STREAM_HEADER
    //  SECBUFFER_DATA
    //  SECBUFFER_STREAM_TRAILER
    //  SECBUFFER_EMPTY
    // Reality is far different.  WinInet passes just 3:  TOKEN/DATA/TOKEN

    // Send the application data, the plaintext, to miTLS
    PVOID pvBuffer = state->pInput->pBuffers[1].pvBuffer;
    DWORD cbBuffer = state->pInput->pBuffers[1].cbBuffer;

    char *outmsg;
    char *errmsg;
    int ret = pfnFFI_mitls_send(state->state, pvBuffer, cbBuffer, &outmsg, &errmsg);
    MITLS_ProcessMessages(outmsg, errmsg);
    if (ret == 0) {
        // Failed
        _Print("MITLS Send failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }
    state->status = SEC_E_OK;
}

void ProcessRecv(TLS_RECV_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    char *outmsg;
    char *errmsg;
    size_t cbReceived;
    VOID *pvReceived = pfnFFI_mitls_receive(state->state, &cbReceived, &outmsg, &errmsg);
    MITLS_ProcessMessages(outmsg, errmsg);
    if (pvReceived == NULL) {
        // Failed
        _Print("MITLS Reecive failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }
    // Copy the data from pvReceived into the output packet
    // Into a SECBUFFER_DATA of the right length
    for (unsigned long i = 0; i < state->pOutput->cBuffers; ++i) {
        PSecBuffer b = &state->pOutput->pBuffers[i];
        if (b->BufferType == SECBUFFER_DATA) {
            _Print("ProcessRecv %d bytes into buffer at %p length %d", (DWORD)cbReceived, b->pvBuffer, b->cbBuffer);
            if (cbReceived > b->cbBuffer) {
                cbReceived = b->cbBuffer;
            }
            memcpy(b->pvBuffer, pvReceived, cbReceived);
            b->cbBuffer = (DWORD)cbReceived;
            break;
        }
    }
    
    pfnFFI_mitls_free_packet(pvReceived);
    state->status = SEC_E_OK;
}

void ProcessDisconnect(TLS_DISCONNECT_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    pfnFFI_mitls_close(state->state);
    state->status = SEC_E_OK;
}

DWORD WINAPI MITLS_Threadproc(
    LPVOID lpThreadParameter
)
{
    ConnectionState *state = (ConnectionState*)lpThreadParameter;

    pfnFFI_mitls_thread_register();

    for (;;) {
        WaitForSingleObject(state->hqueueReady, INFINITE);
        for (;;) {
            EnterCriticalSection(&state->queueLock);
            if (state->mitlsQueue.empty()) {
                LeaveCriticalSection(&state->queueLock);
                break;
            }
            TLS_WORK_ITEM *item = state->mitlsQueue.front();
            state->mitlsQueue.pop();
            LeaveCriticalSection(&state->queueLock);

            switch (item->Type) {
            case TLS_CONNECT:
                ProcessConnect(&item->Connect);
                break;
            case TLS_SEND:
                ProcessSend(&item->Send);
                break;
            case TLS_RECV:
                ProcessRecv(&item->Recv);
                break;
            case TLS_DISCONNECT:
                ProcessDisconnect(&item->Disconnect);
                break;
            case TLS_EXIT_THREAD:
                pfnFFI_mitls_thread_unregister();
                return 0;
            default:
                _Print("Unknown queue item type");
                break;
            }
            SetEvent(item->hWorkItemCompleted);
            // The thread that queued the item is responsible for freeing it
        }
    }
}

BOOL MITLS_Initialize(void)
{
    HMODULE hmitls = LoadLibraryW(L"libmitls.dll");
    if (!hmitls) {
        _Print("Unable to load libmitls - gle=%d", GetLastError());
        return FALSE;
    }
    pfnFFI_mitls_init = (tFFI_mitls_init)GetProcAddress(hmitls, "FFI_mitls_init");
    if (pfnFFI_mitls_init == NULL) {
        _Print("Unable to bind to FFI_mitls_init");
        return FALSE;
    }
    pfnFFI_mitls_cleanup = (tFFI_mitls_cleanup)GetProcAddress(hmitls, "FFI_mitls_cleanup");
    if (pfnFFI_mitls_cleanup == NULL) {
        _Print("Unable to bind to FFI_mitls_cleanup");
        return FALSE;
    }
    pfnFFI_mitls_configure = (tFFI_mitls_configure)GetProcAddress(hmitls, "FFI_mitls_configure");
    if (pfnFFI_mitls_configure == NULL) {
        _Print("Unable to bind to FFI_mitls_configure");
        return FALSE;
    }
    pfnFFI_mitls_connect = (tFFI_mitls_connect)GetProcAddress(hmitls, "FFI_mitls_connect");
    if (pfnFFI_mitls_connect == NULL) {
        _Print("Unable to bind to FFI_mitls_connect");
        return FALSE;
    }
    pfnFFI_mitls_close = (tFFI_mitls_close)GetProcAddress(hmitls, "FFI_mitls_close");
    if (pfnFFI_mitls_close == NULL) {
        _Print("Unable to bind to FFI_mitls_close");
        return FALSE;
    }
    pfnFFI_mitls_send = (tFFI_mitls_send)GetProcAddress(hmitls, "FFI_mitls_send");
    if (pfnFFI_mitls_send == NULL) {
        _Print("Unable to bind to FFI_mitls_send");
        return FALSE;
    }
    pfnFFI_mitls_receive = (tFFI_mitls_receive)GetProcAddress(hmitls, "FFI_mitls_receive");
    if (pfnFFI_mitls_receive == NULL) {
        _Print("Unable to bind to FFI_mitls_receive");
        return FALSE;
    }
    pfnFFI_mitls_free_packet = (tFFI_mitls_free_packet)GetProcAddress(hmitls, "FFI_mitls_free_packet");
    if (pfnFFI_mitls_free_packet == NULL) {
        _Print("Unable to bind to FFI_mitls_free_packet");
        return FALSE;
    }
    pfnFFI_mitls_free_msg = (tFFI_mitls_free_msg)GetProcAddress(hmitls, "FFI_mitls_free_msg");
    if (pfnFFI_mitls_free_msg == NULL) {
        _Print("Unable to bind to FFI_mitls_free_msg");
        return FALSE;
    }
    pfnFFI_mitls_thread_register = (tFFI_mitls_thread_register)GetProcAddress(hmitls, "FFI_mitls_thread_register");
    if (pfnFFI_mitls_thread_register == NULL) {
        _Print("Unable to bind to FFI_mitls_thread_register");
        return FALSE;
    }
    pfnFFI_mitls_thread_unregister = (tFFI_mitls_thread_unregister)GetProcAddress(hmitls, "FFI_mitls_thread_unregister");
    if (pfnFFI_mitls_thread_unregister == NULL) {
        _Print("Unable to bind to FFI_mitls_thread_unregister");
        return FALSE;
    }
    pfnFFI_mitls_get_cert = (tFFI_mitls_get_cert)GetProcAddress(hmitls, "FFI_mitls_get_cert");
    if (pfnFFI_mitls_get_cert == NULL) {
        _Print("Unable to bind to FFI_mitls_get_cert");
        return FALSE;
    }

    int ret = pfnFFI_mitls_init();
    if (ret == 0) {
        _Print("mitls_init failed.  Unable to continue");
        return FALSE;
    }

    return TRUE;
}

void MITLS_ProcessMessages(char *outmsg, char *errmsg)
{
    if (outmsg) {
        _Print("mitls: %s", outmsg);
        pfnFFI_mitls_free_msg(outmsg);
    }
    if (errmsg) {
        _Print("mitls: ERROR %s", errmsg);
        pfnFFI_mitls_free_msg(errmsg);
    }
}

void _PrintPSecBufferDesc(PSecBufferDesc p, bool fDump)
{
    if (!p) {
        return;
    }
    for (ULONG i = 0; i < p->cBuffers; ++i) {
        const char *BufferType = "UNKNOWN";
        switch (p->pBuffers[i].BufferType & (~SECBUFFER_ATTRMASK))
        {
        case SECBUFFER_ALERT: BufferType = "SECBUFFER_ALERT"; break;
        case SECBUFFER_CHANNEL_BINDINGS: BufferType = "SECBUFFER_CHANNEL_BINDINGS"; break;
        case SECBUFFER_CHANGE_PASS_RESPONSE: BufferType = "SECBUFFER_CHANGE_PASS_RESPONSE"; break;
        case SECBUFFER_DATA: BufferType = "SECBUFFER_DATA"; break;
        case SECBUFFER_EMPTY: BufferType = "SECBUFFER_EMPTY"; break;
        case SECBUFFER_EXTRA: BufferType = "SECBUFFER_EXTRA"; break;
        case SECBUFFER_MECHLIST: BufferType = "SECBUFFER_MECHLIST"; break;
        case SECBUFFER_MECHLIST_SIGNATURE: BufferType = "SECBUFFER_MECHLIST_SIGNATURE"; break;
        case SECBUFFER_MISSING: BufferType = "SECBUFFER_MISSING"; break;
        case SECBUFFER_PKG_PARAMS: BufferType = "SECBUFFER_PKG_PARAMS"; break;
        case SECBUFFER_STREAM_HEADER: BufferType = "SECBUFFER_STREAM_HEADER"; break;
        case SECBUFFER_STREAM_TRAILER: BufferType = "SECBUFFER_STREAM_TRAILER"; break;
        case SECBUFFER_TARGET: BufferType = "SECBUFFER_TARGET"; break;
        case SECBUFFER_TARGET_HOST: BufferType = "SECBUFFER_TARGET_HOST"; break;
        case SECBUFFER_TOKEN: BufferType = "SECBUFFER_TOKEN"; break;
        case SECBUFFER_APPLICATION_PROTOCOLS: BufferType = "SECBUFFER_APPLICATION_PROTOCOLS"; break;
        case SECBUFFER_SRTP_PROTECTION_PROFILES: BufferType = "SECBUFFER_SRTP_PROTECTION_PROFILES"; break;
        case SECBUFFER_SRTP_MASTER_KEY_IDENTIFIER: BufferType = "SECBUFFER_SRTP_MASTER_KEY_IDENTIFIER"; break;
        case SECBUFFER_TOKEN_BINDING: BufferType = "SECBUFFER_TOKEN_BINDING"; break;
        case SECBUFFER_PRESHARED_KEY: BufferType = "SECBUFFER_PRESHARED_KEY"; break;
        case SECBUFFER_PRESHARED_KEY_IDENTITY: BufferType = "SECBUFFER_PRESHARED_KEY_IDENTITY"; break;
        default: BufferType = "UNKNOWN"; break;
        }
        _Print("%s(%d) %p %d", BufferType, p->pBuffers[i].BufferType, p->pBuffers[i].pvBuffer, p->pBuffers[i].cbBuffer);
        if (fDump && (p->pBuffers[i].BufferType & 0xfff) == SECBUFFER_DATA) {
            _PrintDump((SOCKET)0, (PCHAR)p->pBuffers[i].pvBuffer, p->pBuffers[i].cbBuffer);
        }
    }
}

// \onecore\ds\security\protocols\ssl\lsamode\sslsspi\ctxtapi.cpp ParseOutputBufferDesc() scans the output buffers to find the
// correct one to write to.
SECURITY_STATUS
ParseOutputBufferDesc(
    __in  PSecBufferDesc pOutput,
    __in  DWORD          dwReqFlags,
    __out PSecBuffer*    ppOutToken)
{
    SECURITY_STATUS dwError = SEC_E_OK;
    PSecBuffer pOutToken = NULL;

    for (DWORD dwIndex = 0; dwIndex < (int)pOutput->cBuffers; ++dwIndex)
    {
        switch ((pOutput->pBuffers[dwIndex].BufferType) & (~(SECBUFFER_ATTRMASK)))
        {
        case SECBUFFER_EMPTY:
            if (!pOutToken && (dwReqFlags & ISC_REQ_ALLOCATE_MEMORY))
            {
                pOutToken = &pOutput->pBuffers[dwIndex];
            }
            break;

        case SECBUFFER_TOKEN:
            pOutToken = &pOutput->pBuffers[dwIndex];
            break;
        }
    }
    if (pOutToken == NULL)
    {
        return SEC_E_INVALID_TOKEN;
    }

    pOutToken->BufferType = SECBUFFER_TOKEN;

    if (dwReqFlags & ISC_REQ_ALLOCATE_MEMORY)
    {
        pOutToken->pvBuffer = NULL;
        pOutToken->cbBuffer = 0;
    }
    else if (pOutToken->pvBuffer == NULL)
    {
        return SEC_E_INSUFFICIENT_MEMORY;
    }

    *ppOutToken = pOutToken;

    return dwError;
}



int MITLS_CALLCONV MITLS_send_callback(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size)
{
    ConnectionState *state = CONTAINING_RECORD(callbacks, ConnectionState, callbacks);
    ULONG BytesCopy = ~0u;

    _Print("MITLS wants to send %p %d", buffer, (int)buffer_size);
    _PrintBuffer(buffer, (int)buffer_size);

    if (state->item->Type == TLS_CONNECT || state->item->Type == TLS_DISCONNECT) { // InitializeSecurityContext()
        PSecBuffer pOutToken;

        pOutToken = state->pOutputBuffer;
        const int max_buffer_size = 16384;
        if (pOutToken->pvBuffer == NULL) {
            PVOID pv = LocalAlloc(LMEM_FIXED, max(buffer_size, max_buffer_size));
            if (!pv) {
                state->status = SEC_E_INSUFFICIENT_MEMORY;
                return -1;
            }
            pOutToken->pvBuffer = pv;
            pOutToken->cbBuffer = (ULONG)buffer_size;
            _Print("MITLS_send_callback - allocated a buffer at %p", pv);
            BytesCopy = min((ULONG)buffer_size, pOutToken->cbBuffer);
            memcpy(pOutToken->pvBuffer, buffer, BytesCopy);
        } else if (state->fContextReq & ISC_REQ_ALLOCATE_MEMORY) {
            if (pOutToken->cbBuffer + buffer_size < max_buffer_size) {
                memcpy((void*)((size_t)pOutToken->pvBuffer + (size_t)pOutToken->cbBuffer), buffer, buffer_size);
                pOutToken->cbBuffer += (DWORD)buffer_size;
                _Print("MITLS_send_callback - appended to buffer at %p", pOutToken->pvBuffer);
                BytesCopy = (ULONG)buffer_size;
            } else {
                _Print("MITLS_send_callback - insufficient space in the buffer!");
                return -1;
            }
        } else {
            BytesCopy = min((ULONG)buffer_size, pOutToken->cbBuffer);
            memcpy(pOutToken->pvBuffer, buffer, BytesCopy);
            _Print("MITLS_send_callback - wrote into preallocated buffer");
        }
        state->status = SEC_I_CONTINUE_NEEDED;
    }
    else if (state->item->Type == TLS_SEND) { // EncryptMessage()
        BytesCopy = 0;
        for (unsigned long i = 0; i < state->pInput->cBuffers; i++) {
            ULONG BufferBytes = min(state->pInput->pBuffers[i].cbBuffer, (ULONG)buffer_size);
            _Print("Copying %d bytes into buffer #%u", BufferBytes, i);

            memcpy(state->pInput->pBuffers[i].pvBuffer, buffer, BufferBytes);
            state->pInput->pBuffers[i].cbBuffer = BufferBytes;
            buffer_size -= (size_t)BufferBytes;
            buffer = (const void*)((size_t)buffer + BufferBytes);
            BytesCopy += BufferBytes;
        }
        state->status = SEC_E_OK;
    } else {
        _Print("Unsupported send state");
    }

    _Print("MITLS_send_callback - Copied %x of %x bytes", BytesCopy, (int)buffer_size);
    // Don't set hOuputReady yet - wait until the MITLS_recv_callback is called by
    // miTLS, in expectation of receiving the reply.  Or in an error case, the MITLS
    // Connect() call may return, at which point, this event should be set too.
    //SetEvent(state->hOutputIsReady);

    return BytesCopy;
}

int MITLS_CALLCONV MITLS_recv_callback(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size)
{
    ConnectionState *state = CONTAINING_RECORD(callbacks, ConnectionState, callbacks);

    _Print("MITLS wants to recv %p %d", buffer, (int)buffer_size);

    _Print("Processing recv");
    if (state->fDeleteOnComplete) {
        _Print("recv() returning failure, to abort a connection in progress.");
        return -1;
    }
    if (state->ActualInputToken.BufferType == SECBUFFER_EMPTY) {
        // Need to fill the internal actual-input buffer with the 
        // calling app's pInput buffer.
        if (state->item->Type == TLS_CONNECT) { // InitializeSecurityContext()
            if (state->pInput == NULL) {
                _Print("Call to InitializeSecurityContext - continue needed");
                state->status = SEC_I_CONTINUE_NEEDED; 
                SetEvent(state->hOutputIsReady);
                // Wait for the next InitializeSecurityContext() call to pass in new buffers.
                WaitForSingleObject(state->hNextCallReady, INFINITE);
            }
            if (state->pInput->cBuffers != 2) {
                _Print("Unexpected pInput->cBuffers %d", state->pInput->cBuffers);
                return -1;
            }
            else if (state->pInput->pBuffers[0].BufferType != SECBUFFER_TOKEN ||
                state->pInput->pBuffers[1].BufferType != SECBUFFER_EMPTY) {
                _Print("Unexpected BufferTypes");
                _PrintPSecBufferDesc(state->pInput);
                __debugbreak();
                return -1;
            }

            memcpy(&state->ActualInputToken, &state->pInput->pBuffers[0], sizeof(SecBuffer));
        } 
        else if (state->item->Type == TLS_RECV) { // DecryptMessage()
            for (unsigned long i = 0; i < state->pOutput->cBuffers; ++i) {
                if (state->pOutput->pBuffers[i].BufferType == SECBUFFER_DATA) {
                    memcpy(&state->ActualInputToken, &state->pOutput->pBuffers[i], sizeof(SecBuffer));
                    break;
                }
            }
        } 
        else {
            _Print("Unsupported recv state");
        }
    }
    PSecBuffer buf = &state->ActualInputToken;
    _Print("Recv secbuffer: %p %d", buf->pvBuffer, buf->cbBuffer);
    size_t length = min(buffer_size, (size_t)buf->cbBuffer);
    memcpy(buffer, buf->pvBuffer, length);
    buf->pvBuffer = (void*)((size_t)buf->pvBuffer + length);
    buf->cbBuffer -= (unsigned long)length;
    if (buf->cbBuffer == 0) {
        if (state->item->Type == TLS_CONNECT) {
            state->pInput->pBuffers[1].BufferType = SECBUFFER_EMPTY;
            state->pInput->pBuffers[1].cbBuffer = 0;
            state->pInput->pBuffers[1].pvBuffer = NULL;
        }
        if (length < buffer_size) {
            _Print("Recv buffer is empty and %d more bytes are needed %s", buffer_size-length, (state->pOutputBuffer->cbBuffer) ? "continue needed" : "incomplete message");
            state->pInput->pBuffers[0].BufferType = SECBUFFER_MISSING;
            state->pInput->pBuffers[0].cbBuffer = (DWORD)buffer_size-(DWORD)length;
            state->pInput->pBuffers[0].pvBuffer = NULL;
            if (state->pOutputBuffer->cbBuffer) { // there are bytes waiting to be sent.  Ask the caller to send them and recv the reply
                state->status = SEC_I_CONTINUE_NEEDED; 
            } else { // there are no bytes waiting to be sent.  We need another recv first.
                state->status = SEC_E_INCOMPLETE_MESSAGE;
            }
            SetEvent(state->hOutputIsReady);
            // Wait for the next InitializeSecurityContext() call to pass in new buffers.
            WaitForSingleObject(state->hNextCallReady, INFINITE);
        } else {
            _Print("Recv buffer is empty and no extra bytes are needed");
            buf->BufferType = SECBUFFER_EMPTY;
            buf->pvBuffer = NULL;
            state->pInput = NULL;
        }
    } else {
        if (state->item->Type == TLS_CONNECT) {
            state->pInput->pBuffers[1].BufferType = SECBUFFER_EXTRA;
            state->pInput->pBuffers[1].cbBuffer = buf->cbBuffer;
            state->pInput->pBuffers[1].pvBuffer = buf->pvBuffer;
        }
    }

    _Print("Received %d bytes OK - caller requested max of %d", (int)length, (int)buffer_size);
    _PrintBuffer(buffer, length);

    return (int)length;
}


#pragma warning(disable:4100)
SECURITY_STATUS
SEC_ENTRY MITLS_InitializeSecurityContextA(
    _In_opt_    PCredHandle phCredential,               // Cred to base context
    _In_opt_    PCtxtHandle phContext,                  // Existing context (OPT)
    _In_opt_    SEC_CHAR * pszTargetName,       // Name of target
    _In_        unsigned long fContextReq,              // Context Requirements
    _In_        unsigned long Reserved1,                // Reserved, MBZ
    _In_        unsigned long TargetDataRep,            // Data rep of target
    _In_opt_    PSecBufferDesc pInput,                  // Input Buffers
    _In_        unsigned long Reserved2,                // Reserved, MBZ
    _Inout_opt_ PCtxtHandle phNewContext,               // (out) New Context handle
    _Inout_opt_ PSecBufferDesc pOutput,                 // (inout) Output Buffers
    _Out_       unsigned long * pfContextAttr,  // (out) Context attrs
    _Out_opt_   PTimeStamp ptsExpiry                    // (out) Life span (OPT)
)
{
    // Useful return values:
    //  SEC_I_CONTINUE_NEEDED - client must send output token to the server and get a response, then call again
    //  SEC_I_COMPLETE_NEEDED - client must call CompleteAuthToken after finishing building the message
    //  SEC_E_INCOMPLETE_MESSAGE - not enough data was read from the socket.  We return a SECBUFFER_MISSING to
    //                             hint at the # of bytes needed to complete the message.
    //  SEC_E_OK - success

    // On first call, pInput should be NULL, and pOutput will be populated on return
    // On subsequent calls, pInput will be a SECBUFFER_TOKEN containing the data received from the server, and a SECBUFFER_EMPTY.
    //__debugbreak();
    ConnectionState *state = NULL;
    TLS_WORK_ITEM *item = NULL;
    
    PSecBuffer pOutputBuffer;
    SECURITY_STATUS st = ParseOutputBufferDesc(pOutput, fContextReq, &pOutputBuffer);
    if (st != SEC_E_OK) {
        return st;
    }
    if (phContext == NULL) {
        _Print("MITLS_InitializeSecurityContextA - initial call");
        MITLS_CredHandle *cred;
        if (phCredential) {
            cred = (MITLS_CredHandle*)phCredential->dwUpper;
        }
        else {
            cred = new MITLS_CredHandle();
            cred->TlsVersion[0] = '\0';
        }
        // First call.  Fill in phNewContext before returning
        state = new ConnectionState();
        InitializeCriticalSection(&state->queueLock);
        state->hqueueReady = CreateEventW(NULL, FALSE, FALSE, NULL);
        state->hOutputIsReady = CreateEventW(NULL, FALSE, FALSE, NULL);
        state->hNextCallReady = CreateEventW(NULL, FALSE, FALSE, NULL); 
        state->cred = cred;
        state->status = SEC_E_INTERNAL_ERROR;
        state->fContextReq = fContextReq;
        state->pInput = pInput; // Note that miTLS ignores these... they may be SECBUFFER_APPLICATION_PROTOCOLS or SECBUFFER_TOKEN_BINDING
        state->pOutput = pOutput;
        state->pOutputBuffer = pOutputBuffer;
        state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
        state->ActualInputToken.pvBuffer = NULL;
        state->ActualInputToken.cbBuffer = 0;
        state->fDeleteOnComplete = false;

        // The documentation indicates that the input buffers must be NULL on first call.  However,
        // Wininet passes a list, which may be empty, or contain SECBUFFER_TOKEN_BINDING and/or
        // SECBUFFER_APPLICATION_PROTOCOLS, to customize the connection.

        item = new TLS_WORK_ITEM();
        state->item = item;
        item->Type = TLS_CONNECT;
        item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
        item->Connect.HostName = pszTargetName;
        item->Connect.state = state;
        EnterCriticalSection(&state->queueLock);
        state->mitlsQueue.push(item);
        LeaveCriticalSection(&state->queueLock);
        SetEvent(state->hqueueReady);

        // Create the worker thread to service this connection
        state->hWorkerThread = CreateThread(NULL, 0, MITLS_Threadproc, state, 0, NULL);
    }
    else {
        _Print("MITLS_InitializeSecurityContextA - continuing call");
        state = (ConnectionState*)phContext->dwUpper;
        if (state->fShuttingDownConnection) {
            item = new TLS_WORK_ITEM();
            state->item = item;
            item->Type = TLS_DISCONNECT;
            item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
            item->Disconnect.state = state;
            EnterCriticalSection(&state->queueLock);
            state->mitlsQueue.push(item);
            LeaveCriticalSection(&state->queueLock);
            SetEvent(state->hqueueReady);
        }
        else {
            if (state->item == NULL) {
                _Print("Error: attempting to continue a non-continuable call");
                return SEC_E_INTERNAL_ERROR;
            }

            item = state->item;
            //state->status = SEC_E_INTERNAL_ERROR;
            state->fContextReq = fContextReq;
            state->pInput = pInput;
            state->pOutput = pOutput;
            state->pOutputBuffer = pOutputBuffer;
            state->ActualInputToken.BufferType = SECBUFFER_EMPTY;

            // Unblock MITLS_recv_callback
            SetEvent(state->hNextCallReady);
        }
    }

    // Now that the item has been queued, wait for the worker thread to process it
    // and tell us what to do next.
    _Print("MITLS_InitializeSecurityContextA - waiting for item");
    HANDLE h[2] = { item->hWorkItemCompleted, state->hOutputIsReady };
    WaitForMultipleObjects(ARRAYSIZE(h), h, FALSE, INFINITE);

    if (state->status == SEC_E_OK) {
        // Finished the work item
        _Print("MITLS_InitializeSecurityContextA - returning SEC_E_OK");
        CloseHandle(item->hWorkItemCompleted);
        phNewContext->dwLower = 0;
        phNewContext->dwUpper = (ULONG_PTR)state;
        delete item;
        state->pInput = state->pOutput = NULL;
        state->item = NULL;
        return state->status;
    }
    else  {
        // Work item is still in progress, but there is data ready to send
        _Print("MITLS_InitializeSecurityContextA - returning %x", state->status);
        if (phNewContext) {
            phNewContext->dwLower = 0;
            phNewContext->dwUpper = (ULONG_PTR)state;
        }
        return state->status;
    }
}

SECURITY_STATUS
SEC_ENTRY MITLS_InitializeSecurityContextW(
    _In_opt_    PCredHandle phCredential,               // Cred to base context
    _In_opt_    PCtxtHandle phContext,                  // Existing context (OPT)
#if ISSP_MODE == 0
    _In_opt_ PSECURITY_STRING pTargetName,
#else
    _In_opt_ SEC_WCHAR * pszTargetName,         // Name of target
#endif
    _In_        unsigned long fContextReq,              // Context Requirements
    _In_        unsigned long Reserved1,                // Reserved, MBZ
    _In_        unsigned long TargetDataRep,            // Data rep of target
    _In_opt_    PSecBufferDesc pInput,                  // Input Buffers
    _In_        unsigned long Reserved2,                // Reserved, MBZ
    _Inout_opt_ PCtxtHandle phNewContext,               // (out) New Context handle
    _Inout_opt_ PSecBufferDesc pOutput,                 // (inout) Output Buffers
    _Out_       unsigned long * pfContextAttr,  // (out) Context attrs
    _Out_opt_   PTimeStamp ptsExpiry                    // (out) Life span (OPT)
)
{
    char TargetName[1024] = { 0 };
    WideCharToMultiByte(CP_ACP, 0, pszTargetName, -1, TargetName, sizeof(TargetName), NULL, NULL);
    return MITLS_InitializeSecurityContextA(phCredential,
        phContext,
        TargetName,
        fContextReq,
        Reserved1,
        TargetDataRep,
        pInput,
        Reserved2,
        phNewContext,
        pOutput,
        pfContextAttr,
        ptsExpiry);
}


SECURITY_STATUS SEC_ENTRY
MITLS_AcquireCredentialsHandleW(
#if ISSP_MODE == 0     // For Kernel mode
    _In_opt_  PSECURITY_STRING pPrincipal,
    _In_      PSECURITY_STRING pPackage,
#else
    _In_opt_  LPWSTR pszPrincipal,                // Name of principal
    _In_      LPWSTR pszPackage,                  // Name of package
#endif
    _In_      unsigned long fCredentialUse,       // Flags indicating use
    _In_opt_  void * pvLogonId,           // Pointer to logon ID
    _In_opt_  void * pAuthData,           // Package specific data
    _In_opt_  SEC_GET_KEY_FN pGetKeyFn,           // Pointer to GetKey() func
    _In_opt_  void * pvGetKeyArgument,    // Value to pass to GetKey()
    _Out_     PCredHandle phCredential,           // (out) Cred Handle
    _Out_opt_ PTimeStamp ptsExpiry                // (out) Lifetime (optional)
)
{
    char *pszPrincipalA;
    char PrincipalA[260]; // bugbug: how long can this be?
    if (pszPrincipal) {
        memset(PrincipalA, 0, sizeof(PrincipalA));
        WideCharToMultiByte(CP_ACP, 0, pszPrincipal, -1, PrincipalA, sizeof(PrincipalA) - 1, NULL, NULL);
        pszPrincipalA = PrincipalA;
    }
    else {
        pszPrincipalA = NULL;
    }
    return MITLS_AcquireCredentialsHandleA(
        PrincipalA,
        UNISP_NAME_A,
        fCredentialUse,
        pvLogonId,
        pAuthData,
        pGetKeyFn,
        pvGetKeyArgument,
        phCredential,
        ptsExpiry);
}

SECURITY_STATUS SEC_ENTRY
MITLS_AcquireCredentialsHandleA(
#if ISSP_MODE == 0     // For Kernel mode
    _In_opt_  PSECURITY_STRING pPrincipal,
    _In_      PSECURITY_STRING pPackage,
#else
    _In_opt_  LPSTR pszPrincipal,                // Name of principal
    _In_      LPSTR pszPackage,                  // Name of package
#endif
    _In_      unsigned long fCredentialUse,       // Flags indicating use
    _In_opt_  void * pvLogonId,           // Pointer to logon ID
    _In_opt_  void * pAuthData,           // Package specific data
    _In_opt_  SEC_GET_KEY_FN pGetKeyFn,           // Pointer to GetKey() func
    _In_opt_  void * pvGetKeyArgument,    // Value to pass to GetKey()
    _Out_     PCredHandle phCredential,           // (out) Cred Handle
    _Out_opt_ PTimeStamp ptsExpiry                // (out) Lifetime (optional)
)
{
    SCHANNEL_CRED c;
    
    // Create a default SCHNANNEL_CRED
    ZeroMemory(&c, sizeof(c));
    c.dwVersion = SCHANNEL_CRED_VERSION;

    if (pAuthData) {
        // pAuthData may have several different types.  The first DWORD disambiguates.
        DWORD dwVersion = *(DWORD*)pAuthData;
        if (dwVersion == SCHANNEL_CRED_VERSION) {
            // Replace the default cred with the app-specified one
            memcpy(&c, (SCHANNEL_CRED*)pAuthData, sizeof(c));
        }
        else if (dwVersion == SEC_WINNT_AUTH_IDENTITY_VERSION) {
            // Do nothing
        }
        else if (dwVersion == SCH_CRED_V3) {
            // Do nothing
        }
        else {
            return SEC_E_UNKNOWN_CREDENTIALS;
        }
    }
    
    // Migrate SCHANNEL_CRED fields into mitls config
    MITLS_CredHandle *h = new MITLS_CredHandle();

    // ->cCreds, ->paCred, ->hRootStore, ->cMappers, ->aphMappers are ignored
    // ->cSupportedAlgs and ->palgSupportedAlgs are ignored
    DWORD dw = GetEnvironmentVariableA("MITLS_SCHANNEL_VERSION", h->TlsVersion, sizeof(h->TlsVersion)); // Set to "1.3" or "1.2"
    if (dw == 0 || dw >= sizeof(h->TlsVersion)) {
        // Variable not found or mal-formed.  Ignore and default to TLS 1.2
        strcpy_s(h->TlsVersion, "1.2");
    }
    _Print("Will connect using TLS %s", h->TlsVersion);
    if (c.grbitEnabledProtocols) {
        _Print("ProcessConfig:  Application has requested its own protocol enabling %x", c.grbitEnabledProtocols);
        // This is where an app can specify the TLS version, client or server, etc.  Assume TLS 1.2 for now.
    }
    // ->dwMinimumCipherStrength, ->dwMaximumCipherStrength are ignored
    // ->dwSessionLifespan is ignored
    // ->dwFlags ignored (validation, reconnects, etc.)
    // ->dwCredFormat ignored

    phCredential->dwLower = 0;
    phCredential->dwUpper = (ULONG_PTR)h;
    if (ptsExpiry) {
        SYSTEMTIME st;
        st.wYear = 30800;
        st.wMonth = 1;
        st.wDayOfWeek = 0;
        st.wDay = 1;
        st.wHour = 0;
        st.wMinute = 0;
        st.wSecond = 0;
        st.wMilliseconds = 0;
        SystemTimeToFileTime(&st, (FILETIME*)ptsExpiry);
    }
    return SEC_E_OK;
}

SECURITY_STATUS SEC_ENTRY
MITLS_FreeCredentialsHandle(
    _In_ PCredHandle phCredential            // Handle to free
)
{
    MITLS_CredHandle *h = (MITLS_CredHandle*)phCredential->dwUpper;
    delete h;
    return SEC_E_OK;
}


SECURITY_STATUS SEC_ENTRY MITLS_FreeContextBuffer(
    _In_ PVOID pvContextBuffer)
{
    // sspicli\newstubs.cxx's implemenation of FreeContextBuffer() directly calls LocalFree() rather
    // than routing to us via pPackage->pftTableW->FreeContextBuffer().  So we must use
    // LocalAlloc()/LocalFree(0 for context buffers too.
    LocalFree(pvContextBuffer);
    return SEC_E_OK;
}


SECURITY_STATUS SEC_ENTRY
MITLS_SetContextAttributesW(
    _In_ PCtxtHandle phContext,                   // Context to Set
    _In_ unsigned long ulAttribute,               // Attribute to Set
    _In_reads_bytes_(cbBuffer) void * pBuffer, // Buffer for attributes
    _In_ unsigned long cbBuffer                   // Size (in bytes) of Buffer
)
{
    // ulAttribute = SECPKG_ATTR_APP_DATA 
    //            or SECPKG_ATTR_EAP_PRF_INFO 
    //            or SECPKG_ATTR_CLIENT_CERT_POLICY 
    //            or SECPKG_ATTR_UI_INFO
    //            or SECPKG_ATTR_EARLY_START
    //            or SECPKG_ATTR_KEYING_MATERIAL_INFO
    if (ulAttribute == SECPKG_ATTR_EARLY_START) {
        return SEC_E_OK; // accept and ignore
    }
    return SEC_E_UNSUPPORTED_FUNCTION;
}

SECURITY_STATUS SEC_ENTRY
MITLS_SetContextAttributesA(
    _In_ PCtxtHandle phContext,                   // Context to Set
    _In_ unsigned long ulAttribute,               // Attribute to Set
    _In_reads_bytes_(cbBuffer) void * pBuffer, // Buffer for attributes
    _In_ unsigned long cbBuffer                   // Size (in bytes) of Buffer
)
{
    return MITLS_SetContextAttributesW(phContext, ulAttribute, pBuffer, cbBuffer);
}

SECURITY_STATUS SEC_ENTRY MITLS_QueryContextAttributesW(
    PCtxtHandle phContext,
    ULONG ulAttribute,
    PVOID pBuffer
)
{
    switch (ulAttribute) {
    case SECPKG_ATTR_REMOTE_CERT_CONTEXT: // pBuffer is a PCERT_CONTEXT
    {
        ConnectionState *state = (ConnectionState*)phContext->dwUpper;

        HCERTSTORE hCertStore = CertOpenStore(CERT_STORE_PROV_MEMORY, 0, NULL, 0, NULL);
        PCCERT_CONTEXT p;
        if (!CertAddEncodedCertificateToStore(hCertStore, 
                                              X509_ASN_ENCODING|PKCS_7_ASN_ENCODING,
                                              state->peer_cert, state->peer_cert_length, 
                                              CERT_STORE_ADD_USE_EXISTING, &p)) {
            DWORD dwErr = GetLastError();
            _Print("CertAddEncodedCertificateToStore failed.  gle=%d(%x).", dwErr, dwErr);
            return SEC_E_INTERNAL_ERROR;
        }
        *(PCCERT_CONTEXT*)pBuffer = p;
        return SEC_E_OK;
    }
    case SECPKG_ATTR_CONNECTION_INFO: // pBuffer is a PSecPkgContext_ConnectionInfo
    {
        // BUGBUG: Fill in from miTLS's state
        PSecPkgContext_ConnectionInfo p = (PSecPkgContext_ConnectionInfo)pBuffer;
        p->dwProtocol = SP_PROT_TLS1_2_CLIENT;
        p->aiCipher = CALG_AES_256;
        p->dwCipherStrength = 256;
        p->aiHash = CALG_SHA;
        p->dwHashStrength = 128;
        p->aiExch = CALG_RSA_KEYX;
        p->dwExchStrength = 2048;
        return SEC_E_OK;
    }
    case SECPKG_ATTR_CIPHER_INFO:
    {
        PSecPkgContext_CipherInfo p = (PSecPkgContext_CipherInfo)pBuffer;
        // BUGBUG: Fill in from miTLS's state
        p->dwVersion = SECPKGCONTEXT_CIPHERINFO_V1;
        p->dwProtocol = SP_PROT_TLS1_2_CLIENT;
#define TLS_RSA_WITH_AES_256_CBC_SHA                0x0035
        p->dwCipherSuite = TLS_RSA_WITH_AES_256_CBC_SHA;
        p->dwBaseCipherSuite = TLS_RSA_WITH_AES_256_CBC_SHA;
        wcscpy_s(p->szCipherSuite, L"miTLS CipherSuite");
        wcscpy_s(p->szCipher, L"miTLS Cipher");
        p->dwCipherLen = 256;
        p->dwCipherBlockLen = 256;
        wcscpy_s(p->szHash, L"miTLS Hash");
        p->dwHashLen = 128;
        wcscpy_s(p->szExchange, L"miTLS Exchange");
        p->dwMinExchangeLen = 2048;
        p->dwMaxExchangeLen = 2048;
        wcscpy_s(p->szCertificate, L"miTLS Certificate");
        p->dwKeyType = 0;
        return SEC_E_OK;
    }
    case SECPKG_ATTR_ENDPOINT_BINDINGS:
    {
        // Wininet ignores the output if the call fails.  It is non-fatal.
        return SEC_E_INVALID_PARAMETER;
    }
    case SECPKG_ATTR_STREAM_SIZES:
    {
        PSecPkgContext_StreamSizes p = (PSecPkgContext_StreamSizes)pBuffer;
        // Values captured from native schannel TLS 1.2.  BUGBUG: Fetch from miTLS
        p->cbBlockSize = 0x10;
        p->cbHeader = 0x15;
        p->cbMaximumMessage = 0x4000;
        p->cbTrailer = 0x40;
        p->cBuffers = 4;
        return SEC_E_OK;
    }
    case SECPKG_ATTR_REMOTE_CERT_CHAIN: // Schannel ignores SEC_E_UNSUPPORTED_FUNCTION failures and converts them to success.
    {
        return SEC_E_UNSUPPORTED_FUNCTION;
    }
    default:
        _Print("QueryContextAttributesW unsupported attribute");
        return SEC_E_INVALID_PARAMETER;
    }
}

SECURITY_STATUS SEC_ENTRY MITLS_QueryContextAttributesA(
    PCtxtHandle phContext,
    ULONG ulAttribute,
    PVOID pBuffer
)
{
    return MITLS_QueryContextAttributesW(phContext, ulAttribute, pBuffer);
}

SECURITY_STATUS SEC_ENTRY MITLS_EncryptMessage(PCtxtHandle         phContext,
    unsigned long       fQOP,
    PSecBufferDesc      pMessage,
    unsigned long       MessageSeqNo)
{
    // Note: schannel is documented as ignoring MessageSeqNo
    MessageSeqNo;

    if (fQOP) {
        _Print("ERROR:  EncryptMessage fQOP not supported"); // bugbug: implement support
        return SEC_E_QOP_NOT_SUPPORTED;
    }
    // Although the SChannel docs for EncryptMessage() state that the buffers must be exactly:
    //  SECBUFFER_STREAM_HEADER
    //  SECBUFFER_DATA
    //  SECBUFFER_STREAM_TRAILER
    //  SECBUFFER_EMPTY
    // Reality is far different.  WinInet passes just 3:  TOKEN/DATA/TOKEN
    if (pMessage->cBuffers < 3) {
        _Print("ERROR: Not enough input buffers to encrypt");
        return SEC_E_DECRYPT_FAILURE;
    } else if (pMessage->pBuffers[1].BufferType != SECBUFFER_DATA) {
        _Print("ERROR: No SECBUFFER_DATA to encrypt");
        return SEC_E_DECRYPT_FAILURE;
    }

    ConnectionState *state = (ConnectionState*)phContext->dwUpper;
    state->pInput = pMessage;
    state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
    TLS_WORK_ITEM *item = new TLS_WORK_ITEM();
    state->item = item;
    item->Type = TLS_SEND;
    item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
    item->Send.state = state;
    SetEvent(state->hNextCallReady);

    EnterCriticalSection(&state->queueLock);
    state->mitlsQueue.push(item);
    LeaveCriticalSection(&state->queueLock);
    SetEvent(state->hqueueReady);

    _Print("MITLS_EncryptMessage - waiting for item");
    WaitForSingleObject(item->hWorkItemCompleted, INFINITE);

    delete item;
    return state->status;
}

SECURITY_STATUS SEC_ENTRY MITLS_DecryptMessage(PCtxtHandle         phContext,
    PSecBufferDesc      pMessage,
    unsigned long       MessageSeqNo,
    unsigned long *     pfQOP)
{
    // Note: schannel is documented as ignoring MessageSeqNo
    MessageSeqNo;

    ConnectionState *state = (ConnectionState*)phContext->dwUpper;
    TLS_WORK_ITEM *item = new TLS_WORK_ITEM();
    state->item = item;
    state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
    state->pOutput = pMessage;
    state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
    item->Type = TLS_RECV;
    item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
    item->Recv.state = state;
    SetEvent(state->hNextCallReady);

    EnterCriticalSection(&state->queueLock);
    state->mitlsQueue.push(item);
    LeaveCriticalSection(&state->queueLock);
    SetEvent(state->hqueueReady);

    _Print("MITLS_DecryptMessage - waiting for item");
    WaitForSingleObject(item->hWorkItemCompleted, INFINITE);

    delete item;
    if (pfQOP) {
        *pfQOP = 0;
    }
    return state->status;
}


SECURITY_STATUS SEC_ENTRY
MITLS_DeleteSecurityContext(
    _In_ PCtxtHandle phContext               // Context to delete
)
{
    ConnectionState *state = (ConnectionState*)phContext->dwUpper;
    phContext->dwLower = phContext->dwUpper = 0;

    if (state->item) {
        _Print("Deleting a SecurityContext for an in-flight InitializeSecurityContext");
        // InitializeSecurity is in progress
        //__debugbreak();
        state->fDeleteOnComplete = true;
        SetEvent(state->hNextCallReady);
    }
    else {
        _Print("Deleting a SecurityContext for an idle connection");
         TLS_WORK_ITEM *item = new TLS_WORK_ITEM();
         item->Type = TLS_EXIT_THREAD;
         EnterCriticalSection(&state->queueLock);
         state->mitlsQueue.push(item);
         LeaveCriticalSection(&state->queueLock);
         SetEvent(state->hqueueReady);   
    }
    return SEC_E_OK;
}

SECURITY_STATUS
SEC_ENTRY
MITLS_ApplyControlToken(
    __in PCtxtHandle    phContext,
    __in PSecBufferDesc pInput
)
{
    // This is used to request disconnection from a TLS peer.
    if (pInput->cBuffers == 1 &&
        pInput->pBuffers[0].BufferType == SECBUFFER_TOKEN &&
        pInput->pBuffers[0].cbBuffer == sizeof(DWORD) &&
        *((DWORD*)pInput->pBuffers[0].pvBuffer) == SCHANNEL_SHUTDOWN) {
        // Shutdown has been requested.  See https://msdn.microsoft.com/en-us/library/windows/desktop/aa380138(v=vs.85).aspx
        // for how this works.  The app will call InitializeSecurityContext() more times, to complete the shutdown.
        _Print("Shutting down miTLS connection");
        ConnectionState *state = (ConnectionState*)phContext->dwUpper;
        state->fShuttingDownConnection = true;
        return SEC_E_OK;
    }
    return SEC_E_UNSUPPORTED_FUNCTION;
}
