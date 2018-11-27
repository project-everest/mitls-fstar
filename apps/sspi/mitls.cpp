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
#include "..\..\src\pki\mipki.h"
}

int MITLS_CALLCONV MITLS_send_callback(void *ctx, const unsigned char *buffer, size_t buffer_size);
int MITLS_CALLCONV MITLS_recv_callback(void *ctx, unsigned char *buffer, size_t buffer_size);

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

typedef struct {
    unsigned long cbBuffer;             // Size of the buffer, in bytes
    unsigned long cbWritten;            // Number of bytes written to the buffer so far
    void *pvBuffer;
} OutputBufferDesc;

typedef struct _ConnectionState {
    // Each connection has an associated worker thread
    std::queue<TLS_WORK_ITEM*> mitlsQueue;
    CRITICAL_SECTION queueLock;
    HANDLE hqueueReady;
    HANDLE hWorkerThread;

    TLS_WORK_ITEM *item; // ptr to work item while InitializeSecurityContext is running, NULL afterwards.
    mitls_state *state;
    mipki_state *pki;

    HANDLE hOutputIsReady;
    HANDLE hNextCallReady;

    // Arguments passed to InitializeSecurityContext
    MITLS_CredHandle *cred;
    PSecBufferDesc pOutput;
    PSecBuffer pOutputBuffer;
    PSecBuffer pApplicationProtocols;
    bool OutputBufferBusy;
    unsigned long fContextReq;
    SECURITY_STATUS status;
    const char *HostName;

    // The pInput buffer to actually read from.  This is initially a copy of the
    // caller's SECBUFFER_TOKEN SecBuffer, but as it is incrementally read from,
    // the buffer pointer and length can change.
    SecBuffer ActualInputToken;
    DWORD cbInputConsumed; // to support SEC_E_INCOMPLETE_MESSAGE

    unsigned int cSendBuffers;
    OutputBufferDesc *pSendOutput;

    bool fShuttingDownConnection;
    bool fDeleteOnComplete;

    BYTE *peer_cert;
    DWORD peer_cert_length;
} ConnectionState;

typedef struct _TLS_CONNECT_WORK_ITEM {
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
    DWORD ThreadId; // thread ID of the thread that queued this work item
    HANDLE hWorkItemCompleted; // bugbug: this is leaked.  This needs to be a class with a destructor

    union {
        TLS_CONNECT_WORK_ITEM Connect;
        TLS_SEND_WORK_ITEM Send;
        TLS_RECV_WORK_ITEM Recv;
        TLS_DISCONNECT_WORK_ITEM Disconnect;
    };

} TLS_WORK_ITEM;

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

SEC_APPLICATION_PROTOCOL_LIST *GetNextList(SEC_APPLICATION_PROTOCOL_LIST *pList)
{
    SEC_APPLICATION_PROTOCOL_LIST *pNext;

    pNext = (SEC_APPLICATION_PROTOCOL_LIST*)((size_t)pList + pList->ProtocolListSize + sizeof(*pList) - sizeof(pList->ProtocolList));

    return pNext;
}

void* MITLS_certificate_select(void *cbs, mitls_version ver,
    const unsigned char *sni, size_t sni_len,
    const unsigned char *alpn, size_t alpn_len,
    const mitls_signature_scheme *sigalgs, size_t sigalgs_len,
    mitls_signature_scheme *selected)
{
    ConnectionState *state = (ConnectionState*)cbs;
    mipki_chain r = mipki_select_certificate(state->pki, (char*)sni, sni_len, sigalgs, sigalgs_len, selected);
    return (void*)r;
}

size_t MITLS_certificate_format(void *cbs, const void *cert_ptr, unsigned char *buffer)
{
    ConnectionState *state = (ConnectionState*)cbs;
    mipki_chain chain = (mipki_chain)cert_ptr;
    return mipki_format_chain(state->pki, chain, (char*)buffer, MAX_CHAIN_LEN);
}

size_t MITLS_certificate_sign(void *cbs, const void *cert_ptr, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, unsigned char *sig)
{
    ConnectionState *state = (ConnectionState*)cbs;
    size_t ret = MAX_SIGNATURE_LEN;

    if (mipki_sign_verify(state->pki, cert_ptr, sigalg, (char*)tbs, tbs_len, (char*)sig, &ret, MIPKI_SIGN))
        return ret;

    return 0;
}

int MITLS_certificate_verify(void *cbs, const unsigned char* chain_bytes, size_t chain_len, const mitls_signature_scheme sigalg, const unsigned char *tbs, size_t tbs_len, const unsigned char *sig, size_t sig_len)
{
    ConnectionState *state = (ConnectionState*)cbs;
    mipki_chain chain = mipki_parse_chain(state->pki, (char*)chain_bytes, chain_len);

    if (chain == NULL)
    {
        _Print("ERROR: failed to parse certificate chain");
        return 0;
    }

    // We don't validate hostname, but could with the callback state
    if (!mipki_validate_chain(state->pki, chain, state->HostName))
    {
        _Print("WARNING: chain validation failed, ignoring.");
        // return 0;
    }

    size_t slen = sig_len;
    int r = mipki_sign_verify(state->pki, chain, sigalg, (char*)tbs, tbs_len, (char*)sig, &slen, MIPKI_VERIFY);
    mipki_free_chain(state->pki, chain);
    return r;
}


void ProcessConnect(TLS_CONNECT_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    _Print("FFI_mitls_configure - TlsVersion=%s hostname=%s", state->cred->TlsVersion, state->HostName);
    int ret = FFI_mitls_configure(&state->state, state->cred->TlsVersion, state->HostName);
    if (ret == 0) {
        // Failed
        _Print("MITLS Configure failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }

    char cipher_suites[512];
    DWORD dw = GetEnvironmentVariableA("MITLS_SCHANNEL_CIPHER_SUITES", cipher_suites, sizeof(cipher_suites));
    if (dw > 0 && dw <  sizeof(cipher_suites)) {
        _Print("Using cipher suites: %s", cipher_suites);
        ret = FFI_mitls_configure_cipher_suites(state->state, cipher_suites);
        if (ret == 0) {
            // Failed
            _Print("MITLS configure_cipher_suites failed");
            state->status = SEC_E_INTERNAL_ERROR;
            return;
        }
    }

    int erridx;
    state->pki = mipki_init(NULL, 0, NULL, &erridx);
    if (!state->pki) {
        _Print("mipki_init failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }

    mitls_cert_cb cert_callbacks = {
        MITLS_certificate_select,
        MITLS_certificate_format,
        MITLS_certificate_sign,
        MITLS_certificate_verify
    };
    ret = FFI_mitls_configure_cert_callbacks(state->state, state, &cert_callbacks);

    if (state->pApplicationProtocols) {
        SEC_APPLICATION_PROTOCOLS  *pProtocols = (SEC_APPLICATION_PROTOCOLS *)state->pApplicationProtocols->pvBuffer;
        SEC_APPLICATION_PROTOCOL_LIST *pListStart = &pProtocols->ProtocolLists[0];
        SEC_APPLICATION_PROTOCOL_LIST *pListEnd = (SEC_APPLICATION_PROTOCOL_LIST*)((size_t)pListStart + pProtocols->ProtocolListsSize);
            
        for (SEC_APPLICATION_PROTOCOL_LIST *pList = pListStart; pList < pListEnd;pList = GetNextList(pList)) {
            switch (pList->ProtoNegoExt) {
            case SecApplicationProtocolNegotiationExt_ALPN:
                mitls_alpn alpn;

                alpn.alpn = pList->ProtocolList,
                alpn.alpn_len = strlen((const char*)pList->ProtocolList);
                ret = FFI_mitls_configure_alpn(state->state, &alpn, 1);
                if (ret == 0) {
                    _Print("FFI_mitls_configure_alpn failed");
                    state->status = SEC_E_INTERNAL_ERROR;
                    return;
                }
                break;
            case SecApplicationProtocolNegotiationExt_NPN:
                _Print("NPN extention is not supported by miTLS - ignoring");
                break;
            case SecApplicationProtocolNegotiationExt_None:
                // Ignore.  Applications sometimes allocate space for multiple extensions
                // then only fill in one, leaving the rest set to _None.
                break;
            default:
                _Print("Unknown/unsupported Application Protocol Extension %d - ignoring.", pList->ProtoNegoExt);
                break;
            }
        }
    }

    ret = FFI_mitls_connect(state,
                            MITLS_send_callback,
                            MITLS_recv_callback,
                            state->state);
    if (ret == 0) {
        // Failed
        _Print("MITLS Connect failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }
    _Print("FFI_mitls_get_cert");
    size_t cb;
    void *pb = FFI_mitls_get_cert(state->state, &cb);
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
    const unsigned char *pvBuffer = (const unsigned char *)state->ActualInputToken.pvBuffer;
    DWORD cbBuffer = state->ActualInputToken.cbBuffer;

    int ret = FFI_mitls_send(state->state, pvBuffer, cbBuffer);
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

    size_t cbReceived;

    unsigned char *pReceived = FFI_mitls_receive(state->state, &cbReceived);
    if (pReceived == NULL) {
        // Failed
        _Print("MITLS Receive failed");
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    }

    void* OutputBuffer = NULL;
    size_t cbOutputBuffer = 0;
    for (ULONG i = 0; i < state->pOutput->cBuffers; ++i) {
        if (state->pOutput->pBuffers[i].BufferType == SECBUFFER_DATA) {
            OutputBuffer = state->pOutput->pBuffers[i].pvBuffer;
            cbOutputBuffer = state->pOutput->pBuffers[i].cbBuffer;
            break;
        }
    }
    if (!OutputBuffer) {
        _Print("Couldn't find a SECBUFFER_DATA to write into!");
        FFI_mitls_free(state->state, pReceived);
        state->status = SEC_E_INTERNAL_ERROR;
        return;
    } else if (cbOutputBuffer < cbReceived) {
        cbReceived = cbOutputBuffer;
    }

    // Copy the data from pvReceived into the output packet
    // Into a SECBUFFER_DATA of the right length
    if (state->pOutput->cBuffers) {
        state->pOutput->pBuffers[0].BufferType = SECBUFFER_STREAM_HEADER;
        state->pOutput->pBuffers[0].cbBuffer = 0;
        state->pOutput->pBuffers[0].pvBuffer = NULL;
        if (state->pOutput->cBuffers > 1) {
            state->pOutput->pBuffers[1].BufferType = SECBUFFER_DATA;
            state->pOutput->pBuffers[1].cbBuffer = (ULONG)cbReceived;
            state->pOutput->pBuffers[1].pvBuffer = OutputBuffer;
            memcpy(OutputBuffer, pReceived, cbReceived);
            if (state->pOutput->cBuffers > 2) {
                state->pOutput->pBuffers[2].BufferType = SECBUFFER_STREAM_TRAILER;
                state->pOutput->pBuffers[2].cbBuffer = 0;
                state->pOutput->pBuffers[2].pvBuffer = NULL;
                if (state->pOutput->cBuffers > 3 && state->ActualInputToken.cbBuffer) {
                    state->pOutput->pBuffers[3].BufferType = SECBUFFER_EXTRA;
                    state->pOutput->pBuffers[3].cbBuffer = state->ActualInputToken.cbBuffer;
                    state->pOutput->pBuffers[3].pvBuffer = state->ActualInputToken.pvBuffer;
                }
            }
        }
    }

    FFI_mitls_free(state->state, pReceived);
    state->status = SEC_E_OK;
}

void ProcessDisconnect(TLS_DISCONNECT_WORK_ITEM* item)
{
    ConnectionState *state = item->state;

    FFI_mitls_close(state->state);
    state->item = NULL;
    state->state = NULL;
    state->status = SEC_E_OK;
    free((void*)state->HostName);
}

DWORD WINAPI MITLS_Threadproc(
    LPVOID lpThreadParameter
)
{
    ConnectionState *state = (ConnectionState*)lpThreadParameter;

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
                SetEvent(item->hWorkItemCompleted);
                break;
            case TLS_SEND:
                ProcessSend(&item->Send);
                SetEvent(item->hWorkItemCompleted);
                break;
            case TLS_RECV:
                ProcessRecv(&item->Recv);
                SetEvent(item->hWorkItemCompleted);
                break;
            case TLS_DISCONNECT:
                ProcessDisconnect(&item->Disconnect);
                SetEvent(item->hWorkItemCompleted);
                break;
            case TLS_EXIT_THREAD:
                delete item;
                state->item = NULL;
                return 0;
            default:
                _Print("Unknown queue item type");
                break;
            }

            // The thread that queued the item is responsible for freeing it
        }
    }
}

void MITLS_CALLCONV TraceCallback(const char *msg)
{
    _Print("%s", msg);
}

BOOL MITLS_Initialize(void)
{
    FFI_mitls_set_trace_callback(TraceCallback);
    int ret = FFI_mitls_init();
    if (ret == 0) {
        _Print("mitls_init failed.  Unable to continue");
        return FALSE;
    }

    return TRUE;
}

void _PrintPSecBuffer(PSecBuffer b , bool fDump)
{
    const char *BufferType = "UNKNOWN";
    switch (b->BufferType & (~SECBUFFER_ATTRMASK)) {
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
    _Print("%s(%d) %p %d", BufferType, b->BufferType, b->pvBuffer, b->cbBuffer);
    if (fDump && (b->BufferType & 0xfff) != SECBUFFER_EMPTY) {
        _PrintDump((SOCKET)0, (PCHAR)b->pvBuffer, b->cbBuffer);
    }
}

void _PrintPSecBufferDesc(const char *label, PSecBufferDesc p, bool fDump)
{
    _Print("PSecBufferDesc %p: %s", p, label);
    if (!p) {
        return;
    }
    for (ULONG i = 0; i < p->cBuffers; ++i) {
        _PrintPSecBuffer(&p->pBuffers[i], fDump);
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



int MITLS_CALLCONV MITLS_send_callback(void *ctx, const unsigned char *buffer, size_t buffer_size)
{
    ConnectionState *state = (ConnectionState*)ctx;

    _Print("MITLS wants to send %p %d", buffer, (int)buffer_size);
    _PrintBuffer(buffer, (int)buffer_size);

    if (state->fDeleteOnComplete) {
        _Print("TLS connection has been terminated.  Ignore writes.");
        return (int)buffer_size;
    }

    if (state->item->Type == TLS_SEND) {
        const unsigned char *pb = buffer;
        unsigned int cb = (unsigned int)buffer_size;
        for (ULONG i = 0; cb && i < state->cSendBuffers; ++i) {
            unsigned int cbcopy = min(cb, (state->pSendOutput[i].cbBuffer-state->pSendOutput[i].cbWritten));
            if (cbcopy) {
                void *pvDest = (void*)((intptr_t)state->pSendOutput[i].pvBuffer + state->pSendOutput[i].cbWritten);
                memcpy(pvDest, pb, cbcopy);
                state->pSendOutput[i].cbWritten += cbcopy;
                pb += cbcopy;
                cb -= cbcopy;
            }
        }
        if (cb) {
            _Print("Insufficient buffer space in pOutput");
            state->status = SEC_E_BUFFER_TOO_SMALL;
            return -1;
        }
        return (int)buffer_size;
    }
    // Else InitializeSecurityContext

    if (state->OutputBufferBusy) {
        // bugbug: this is a mess.  Need to keep a write pointer into pOutputBuffer and move it along
        size_t newsize = state->pOutputBuffer->cbBuffer + buffer_size;
        PVOID pv = LocalAlloc(LMEM_FIXED, newsize);
        if (!pv) {
            state->status = SEC_E_INSUFFICIENT_MEMORY;
            return -1;
        }
        memcpy(pv, state->pOutputBuffer->pvBuffer, state->pOutputBuffer->cbBuffer);
        memcpy((void*)((size_t)pv + state->pOutputBuffer->cbBuffer), buffer, buffer_size);
        state->pOutputBuffer->cbBuffer = (DWORD)newsize;
        LocalFree(state->pOutputBuffer->pvBuffer);
        state->pOutputBuffer->pvBuffer = pv;
        _Print("MITLS_send_callback - append success");
        return (int)buffer_size;
    }
    PSecBuffer pOutToken = state->pOutputBuffer;
    if (pOutToken->pvBuffer == NULL) {
        if (state->fContextReq & ISC_REQ_ALLOCATE_MEMORY) {
            PVOID pv = LocalAlloc(LMEM_FIXED, buffer_size);
            if (!pv) {
                state->status = SEC_E_INSUFFICIENT_MEMORY;
                return -1;
            }
            pOutToken->pvBuffer = pv;
            pOutToken->cbBuffer = (ULONG)buffer_size;
            _Print("MITLS_send_callback - allocated a buffer at %p", pv);
        } else {
            _Print("MITLS_send_callback - NULL pvBuffer and ISC_REQ_ALLOCATE_MEMORY not set");
            state->status = SEC_E_INTERNAL_ERROR;
            return -1;
        }
    } else if (pOutToken->cbBuffer < buffer_size) {
        _Print("MITLS_send_callback - insufficient pOutputBuffer to store the token");
        __debugbreak();
        state->status = SEC_E_INTERNAL_ERROR;
        return -1;
    }
    memcpy(pOutToken->pvBuffer, buffer, buffer_size);
    if (pOutToken->BufferType != SECBUFFER_TOKEN) {
        pOutToken->BufferType = SECBUFFER_DATA; // indicate that the buffer contains data
    }
    pOutToken->cbBuffer = (DWORD)buffer_size;
    state->OutputBufferBusy = true;

    _Print("MITLS_send_callback - success");
    // Don't set hOuputReady yet - wait until the MITLS_recv_callback is called by
    // miTLS, in expectation of receiving the reply.  Or in an error case, the MITLS
    // Connect() call may return, at which point, this event should be set too.
    //SetEvent(state->hOutputIsReady);

    return (int)buffer_size;
}

int MITLS_CALLCONV MITLS_recv_callback(void *ctx, unsigned char *buffer, size_t buffer_size)
{
    ConnectionState *state = (ConnectionState*)ctx;

    _Print("MITLS wants to recv %p %d", buffer, (int)buffer_size);

    if (state->fDeleteOnComplete) {
    AbortRecv:
        _Print("recv() returning failure, to abort a connection in progress.");
        return -1;
    }

    if (state->OutputBufferBusy) {
        _Print("But first, send the current output buffer");
        _PrintPSecBuffer(state->pOutputBuffer);
        state->status = SEC_I_CONTINUE_NEEDED;
        SetEvent(state->hOutputIsReady);
        WaitForSingleObject(state->hNextCallReady, INFINITE);
        if (state->fDeleteOnComplete) {
            goto AbortRecv;
        }
    }

    if (state->ActualInputToken.cbBuffer < buffer_size && state->item->Type == TLS_CONNECT) {
        // Although the docs for InitializeSecurityContext() say SEC_E_INCOMPLETE_MESSAGE
        // is returned if the whole message hasn't been read, it really returns
        // SEC_I_CONTINUE_NEEDED with a 0-byte output buffer, to begin reading from a
        // fresh TLS record.
        _Print("Insufficient data ready for read, during handshake.  Use SEC_I_CONTINUE_NEEDED\n");
        _PrintPSecBuffer(state->pOutputBuffer);
        state->status = SEC_I_CONTINUE_NEEDED;
        SetEvent(state->hOutputIsReady);
        WaitForSingleObject(state->hNextCallReady, INFINITE);
        if (state->fDeleteOnComplete) {
            goto AbortRecv;
        }
    }

    while (state->ActualInputToken.cbBuffer < buffer_size) {
        if (state->OutputBufferBusy) {
            _Print("Unexpected send() inside a recv() loop");
            __debugbreak();
        }

        state->ActualInputToken.BufferType = SECBUFFER_MISSING;
        state->ActualInputToken.cbBuffer = (DWORD)(buffer_size - state->ActualInputToken.cbBuffer);
        state->ActualInputToken.pvBuffer = NULL;
        state->status = SEC_E_INCOMPLETE_MESSAGE;
        _Print("Recv is out of buffers.  Requesting %d more", state->ActualInputToken.cbBuffer);
        SetEvent(state->hOutputIsReady);
        // Wait for the next InitializeSecurityContext() call to pass in new buffers.
        WaitForSingleObject(state->hNextCallReady, INFINITE);
        if (state->fDeleteOnComplete) {
            goto AbortRecv;
        }
        _Print("Back from reciving more data");
        if (state->ActualInputToken.cbBuffer < state->cbInputConsumed) {
            _Print("New buffer is smaller than the consumed input!");
            __debugbreak();
        }
        state->ActualInputToken.pvBuffer = (void*)((size_t)state->ActualInputToken.pvBuffer + state->cbInputConsumed);
        state->ActualInputToken.cbBuffer -= (ULONG)state->cbInputConsumed;
        state->ActualInputToken.BufferType = SECBUFFER_EXTRA;
    }
    _Print("Recv from buffer");
    _PrintPSecBuffer(&state->ActualInputToken);

    // Fill in the data
    memcpy(buffer, state->ActualInputToken.pvBuffer, buffer_size);

    state->ActualInputToken.pvBuffer = (void*)((size_t)state->ActualInputToken.pvBuffer + buffer_size);
    state->ActualInputToken.cbBuffer -= (ULONG)buffer_size;
    state->ActualInputToken.BufferType = SECBUFFER_EXTRA;
    state->cbInputConsumed += (DWORD)buffer_size;

    _Print("Received OK");
    _PrintBuffer(buffer, buffer_size);

    return (int)buffer_size;
}

SECURITY_STATUS ParseInputBufferDesc(PSecBufferDesc pInput, ULONG DataBufferType, PSecBuffer pActualInput, PSecBuffer* ppApplicationProtocols)
{
    pActualInput->BufferType = SECBUFFER_EMPTY;
    pActualInput->cbBuffer = 0;
    pActualInput->pvBuffer = NULL;
    
    *ppApplicationProtocols = NULL;

    if (pInput == NULL) {
        return SEC_E_OK;
    }

    for (ULONG i = 0; i < pInput->cBuffers; ++i) {
        if (pInput->pBuffers[i].BufferType == DataBufferType) {
            memcpy(pActualInput, &pInput->pBuffers[i], sizeof(*pActualInput));
        }
        switch (pInput->pBuffers[i].BufferType) {
            case SECBUFFER_TOKEN:
                break;
            case SECBUFFER_DATA:
                break;
            case SECBUFFER_EMPTY:
                break;
            case SECBUFFER_STREAM_HEADER:
                break;
            case SECBUFFER_STREAM_TRAILER:
                break;
            case SECBUFFER_APPLICATION_PROTOCOLS:
                *ppApplicationProtocols = &pInput->pBuffers[i];
                break;
            case SECBUFFER_TOKEN_BINDING:
                // Skip these buffers
                _Print("Skipping SECBUFFER_TOKEN_BINDING");
                break;
            default:
                _Print("Unexpected BufferType at %u", i);
                _PrintPSecBufferDesc("pInput", pInput);
                __debugbreak();
                return SEC_E_INVALID_PARAMETER;
        }
    }
    return SEC_E_OK;
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
    SecBuffer ActualInput;
    PSecBuffer pApplicationProtocols;
    st = ParseInputBufferDesc(pInput, SECBUFFER_TOKEN, &ActualInput, &pApplicationProtocols);
    if (st != SEC_E_OK) {
        return st;
    }
    if (phContext == NULL) {
        _Print("MITLS_InitializeSecurityContextA - initial call");
        _PrintPSecBufferDesc("pInput", pInput);
        _PrintPSecBufferDesc("pOutput", pOutput);
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
        state->ActualInputToken = ActualInput;
        state->cbInputConsumed = 0;
        state->pOutput = pOutput;
        state->pOutputBuffer = pOutputBuffer;
        state->OutputBufferBusy = false;
        state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
        state->ActualInputToken.pvBuffer = NULL;
        state->ActualInputToken.cbBuffer = 0;
        state->fDeleteOnComplete = false;
        state->pApplicationProtocols = pApplicationProtocols;
        state->HostName = _strdup(pszTargetName);

        // The documentation indicates that the input buffers must be NULL on first call.  However,
        // Wininet passes a list, which may be empty, or contain SECBUFFER_TOKEN_BINDING and/or
        // SECBUFFER_APPLICATION_PROTOCOLS, to customize the connection.

        item = new TLS_WORK_ITEM();
        state->item = item;
        item->Type = TLS_CONNECT;
        item->ThreadId = GetCurrentThreadId();
        item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
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
        _PrintPSecBufferDesc("pInput", pInput);
        _PrintPSecBufferDesc("pOutput", pOutput);
        state = (ConnectionState*)phContext->dwUpper;
        if (state->fShuttingDownConnection) {
            item = new TLS_WORK_ITEM();
            state->item = item;
            item->Type = TLS_DISCONNECT;
            item->ThreadId = GetCurrentThreadId();
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
            state->ActualInputToken = ActualInput;
            state->pOutput = pOutput;
            state->pOutputBuffer = pOutputBuffer;
            state->OutputBufferBusy = false;
            state->ActualInputToken = ActualInput;

            // Unblock MITLS_recv_callback
            _Print("Unblock nextCallReady %p from InitializeSecurityContext resume", state->hNextCallReady);
            SetEvent(state->hNextCallReady);
        }
    }

    // Now that the item has been queued, wait for the worker thread to process it
    // and tell us what to do next.
    _Print("MITLS_InitializeSecurityContextA - waiting for item");
    HANDLE h[2] = { item->hWorkItemCompleted, state->hOutputIsReady };
    WaitForMultipleObjects(ARRAYSIZE(h), h, FALSE, INFINITE);

    *pfContextAttr = fContextReq;

    if (state->status == SEC_E_OK) {
        // Finished the work item
        _Print("MITLS_InitializeSecurityContextA - returning SEC_E_OK");
        CloseHandle(item->hWorkItemCompleted);
        phNewContext->dwLower = 0;
        phNewContext->dwUpper = (ULONG_PTR)state;
        delete item;
        state->item = NULL;
        state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
        state->ActualInputToken.cbBuffer = 0;
        state->ActualInputToken.pvBuffer = NULL;
        state->cbInputConsumed = 0;
        state->pOutput = NULL;
        state->OutputBufferBusy = false;
        state->item = NULL;
        return state->status;
    }
    else  {
        // Work item is still in progress, but there is data ready to send
        if (pInput && state->ActualInputToken.BufferType != SECBUFFER_EMPTY && state->ActualInputToken.cbBuffer != 0) {
            for (ULONG i = 0; i < pInput->cBuffers; ++i) {
                if (pInput->pBuffers[i].BufferType == SECBUFFER_EMPTY) {
                    _Print("Updating pInput with fresh ActualInputToken");
                    memcpy(&pInput->pBuffers[i], &state->ActualInputToken, sizeof(SecBuffer));
                    break;
                }
            }
        }
        _Print("MITLS_InitializeSecurityContextA - returning %x", state->status);
        _PrintPSecBufferDesc("pInput", pInput);
        _PrintPSecBufferDesc("pOutput", pOutput);
        if (phNewContext) {
            phNewContext->dwLower = 0;
            phNewContext->dwUpper = (ULONG_PTR)state;
        }
        if (state->status != SEC_E_INCOMPLETE_MESSAGE) {
            _Print("Resetting cbInputConsumed");
            state->cbInputConsumed = 0;
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
    if (ulAttribute == SECPKG_ATTR_EARLY_START ||
        ulAttribute == SECPKG_ATTR_UI_INFO) {
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
        p->cbHeader = 0x15; //  0xd;
        p->cbMaximumMessage = 0x4000;
        p->cbTrailer = 0x40; // 0x10;
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
    } if (pMessage->cBuffers > 4) {
        _Print("ERROR: Too many input buffers to encrypt");
        return SEC_E_DECRYPT_FAILURE;
    }
    SecBuffer ActualInput;
    PSecBuffer pApplicationProtocols;
    SECURITY_STATUS st = ParseInputBufferDesc(pMessage, SECBUFFER_DATA, &ActualInput, &pApplicationProtocols);
    if (st != SEC_E_OK) {
        return st;
    }

    OutputBufferDesc pOutputs[4];
    for (unsigned int i = 0; i < pMessage->cBuffers; ++i) {
        pOutputs[i].cbBuffer = pMessage->pBuffers[i].cbBuffer;
        pOutputs[i].pvBuffer = pMessage->pBuffers[i].pvBuffer;
        pOutputs[i].cbWritten = 0;
    }

    ConnectionState *state = (ConnectionState*)phContext->dwUpper;
    state->ActualInputToken = ActualInput;
    state->cbInputConsumed = 0;
    TLS_WORK_ITEM *item = new TLS_WORK_ITEM();
    state->item = item;
    state->pOutputBuffer = NULL;
    state->pOutput = NULL;
    state->OutputBufferBusy = false;
    state->cSendBuffers = pMessage->cBuffers;
    state->pSendOutput = pOutputs;
    item->Type = TLS_SEND;
    item->ThreadId = GetCurrentThreadId();
    item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
    item->Send.state = state;
    //_Print("Unblock nextCallReady %p from EncryptMessage", state->hNextCallReady);
    //SetEvent(state->hNextCallReady);

    EnterCriticalSection(&state->queueLock);
    state->mitlsQueue.push(item);
    LeaveCriticalSection(&state->queueLock);
    SetEvent(state->hqueueReady);

    _Print("MITLS_EncryptMessage - waiting for item");
    WaitForSingleObject(item->hWorkItemCompleted, INFINITE);
    _Print("MITLS_EncryptMessage - done");

    for (unsigned int i = 0; i < pMessage->cBuffers; ++i) {
        pMessage->pBuffers[i].cbBuffer = pOutputs[i].cbWritten;
    }

    delete item;
    state->item = NULL;
    return state->status;
}

//  On entry, pMessage is an array of 4 elements:  SECBUFFER_DATA, and 3 SECBUFFER_EMPTY
//  On return, those are replaced by header, data, trailer, and extra
SECURITY_STATUS SEC_ENTRY MITLS_DecryptMessage(PCtxtHandle         phContext,
    PSecBufferDesc      pMessage,
    unsigned long       MessageSeqNo,
    unsigned long *     pfQOP) {
    // Note: schannel is documented as ignoring MessageSeqNo
    MessageSeqNo;

    SecBuffer ActualInput;
    PSecBuffer pApplicationProtocols;
    SECURITY_STATUS st = ParseInputBufferDesc(pMessage, SECBUFFER_DATA, &ActualInput, &pApplicationProtocols);
    if (st != SEC_E_OK) {
        return st;
    }

    ConnectionState *state = (ConnectionState*)phContext->dwUpper;
    state->ActualInputToken = ActualInput;
    state->pOutput = pMessage;
    state->OutputBufferBusy = false;
    state->ActualInputToken.BufferType = SECBUFFER_EMPTY;
    TLS_WORK_ITEM *item = state->item;
    if (!item)  {
        item = new TLS_WORK_ITEM();
        item->ThreadId = GetCurrentThreadId();
        item->Type = TLS_RECV;
        item->hWorkItemCompleted = CreateEventW(NULL, FALSE, FALSE, NULL);
        item->Recv.state = state;
        state->item = item;
        state->cbInputConsumed = 0;

        EnterCriticalSection(&state->queueLock);
        state->mitlsQueue.push(item);
        LeaveCriticalSection(&state->queueLock);
        SetEvent(state->hqueueReady);
    } else if (item->Type != TLS_RECV) {
        _Print("Error!  Unexpected item type for continuation");
        __debugbreak();
    } else {
        _Print("Unblock nextCallReady %p from DecryptMessage", state->hNextCallReady);
        SetEvent(state->hNextCallReady);
    }

    _Print("MITLS_DecryptMessage - waiting for item");
    HANDLE h[2] = { item->hWorkItemCompleted, state->hOutputIsReady };
    WaitForMultipleObjects(ARRAYSIZE(h), h, FALSE, INFINITE);
    if (state->status == SEC_E_OK) {
        delete item;
        state->item = NULL;
        if (pfQOP) {
            *pfQOP = 0;
        }
        _Print("Decrypted: %x", state->status);
        return state->status;
    } else {
        _Print("Not yet decrypted: %x", state->status);
        // Work item is still in progress, but there is data ready to send
        if (state->ActualInputToken.BufferType != SECBUFFER_EMPTY && state->ActualInputToken.cbBuffer != 0) {
            for (ULONG i = 0; i < pMessage->cBuffers; ++i) {
                if (pMessage->pBuffers[i].BufferType == SECBUFFER_EMPTY) {
                    _Print("Updating pMessage with fresh ActualInputToken");
                    memcpy(&pMessage->pBuffers[i], &state->ActualInputToken, sizeof(SecBuffer));
                    break;
                }
            }
        }
        return state->status;
    }
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
        _Print("Unblock nextCallReady %p from DeleteSecurityContext", state->hNextCallReady);
        SetEvent(state->hNextCallReady);
    }
    else {
        _Print("Deleting a SecurityContext for an idle connection");
         TLS_WORK_ITEM *item = new TLS_WORK_ITEM();
         item->Type = TLS_EXIT_THREAD;
         item->ThreadId = GetCurrentThreadId();
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
