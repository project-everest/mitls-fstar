

#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "bio_lcl.h"
#include "openssl/bio.h"

#include "mitlsffi.h"

#ifdef _WIN32
__declspec(dllexport) 
#endif
void* getAddress( void* pointer ){
	return pointer;
}

#ifdef _WIN32
__declspec(dllexport) 
#endif
char* duplicateString( char* source, uint32_t size /* including terminating NULL */ ) {
	// printf("########## %s in %s: %d; size = %d, source = %s \n", __FILE__, __FUNCTION__, __LINE__, size, source	 );
	char *dest = malloc( size );
	
	if( NULL == dest )
		return NULL;

	memcpy( dest, source, size );
	
	return dest;
}

char* DuplicateString_unsafe( char *source )
{
  return duplicateString( source, strlen( source ) + 1 );
}

quic_config* QuicConfigCreate(  char*        serverCertPath,
                                char*        serverKeyPath,
                                char*        serverCAPath,
                                char*        supportedCipherSuites,
                                char*        supportedSignatureAlgorithms,
                                char*        supportedNamedGroups,
                                char*        hostName,
                                uint32_t     isServer,
                                quic_ticket *server_ticket  )
{
    quic_config *config = malloc( sizeof( quic_config )) ;
    memset( config, 0, sizeof(quic_config));

    config->is_server               = isServer;
    config->host_name               = DuplicateString_unsafe( hostName);
    config->qp.max_stream_data      = 16000;
    config->qp.max_data             = 32000;
    config->qp.max_stream_id        = 16;
    config->qp.idle_timeout         = 60;
    config->server_ticket.len       = 0;
    config->certificate_chain_file  = DuplicateString_unsafe( serverCertPath                );
    config->private_key_file        = DuplicateString_unsafe( serverKeyPath                 );
    config->ca_file                 = DuplicateString_unsafe( serverCAPath                  );
    config->cipher_suites           = DuplicateString_unsafe( supportedCipherSuites         );
    config->signature_algorithms    = DuplicateString_unsafe( supportedSignatureAlgorithms  );
    config->named_groups            = DuplicateString_unsafe( supportedNamedGroups          );
    config->ticket_enc_alg          = NULL;
    config->ticket_key              = NULL;
    config->ticket_key_len          = 0;
    config->enable_0rtt             = 1;

    if( server_ticket != NULL ) {
        config->server_ticket       = *server_ticket;
    }

    return config;
}



#ifdef _WIN32
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
DWORD read_file_of_fixed_size( char* fname, void** buffer, DWORD expected_size )
{
  HANDLE hFile = CreateFile (fname, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);

  if (hFile == INVALID_HANDLE_VALUE) {
    printf ("ERROR: unable to open file %s\n", fname);
    ExitProcess(1);
  }

  DWORD size = GetFileSize(hFile, 0);
  if (expected_size != 0 && size != expected_size) {
    printf ("file %s has size %d; expected size %d\n", fname, size, expected_size);
    ExitProcess(1);
  }

  *buffer = malloc(size);

  DWORD read;
  BOOL res = ReadFile(hFile, *buffer, size, &read, NULL);
  if (res == FALSE) {
    printf ("ERROR: unable to read file %s\n", fname);
    ExitProcess(1);
  }
  CloseHandle(hFile);

  return size;
}

__declspec(dllexport) 
DWORD ReadFromFile(char *filePath, char **buffer)
{
	printf("########## %s in %s: %d; filePath = %s \n", __FILE__, __FUNCTION__, __LINE__, filePath );
	DWORD fileSize = read_file_of_fixed_size( filePath, (void**)buffer, 0);
	printf("########## %s in %s: %d; fileSize = %d \n", __FILE__, __FUNCTION__, __LINE__, fileSize );

	return fileSize;
}
#endif

#ifdef _WIN32
__declspec(dllexport) 
#endif
void* DoMemcpy( void* dest, void* src, size_t size )
{
	printf("########## %s in %s: %d; dest = %p; src = %p; size = %ld\n", __FILE__, __FUNCTION__, __LINE__, dest, src, size );
	return memcpy( dest, src, size );
}

int sock_new(BIO *bi)
{
    bi->init = 0;
    bi->num = 0;
    bi->ptr = NULL;
    bi->flags = 0;
    return (1);
}

int sock_free(BIO *a)
{
    if (a == NULL)
        return (0);
    if (a->shutdown) {
        if (a->init) {
            printf("########## %s in %s: %d; closing fake socket %d\n", __FILE__, __FUNCTION__, __LINE__, a->num );
            // BIO_closesocket(a->num);
        }
        a->init = 0;
        a->flags = 0;
    }
    return (1);
}

long sock_ctrl(BIO *b, int cmd, long num, void *ptr)
{
    printf("########## %s in %s: %d;\n", __FILE__, __FUNCTION__, __LINE__ );
    long ret = 1;
    int *ip;

    switch (cmd) {
    case BIO_C_SET_FD:
        sock_free(b);
        b->num = *((int *)ptr);
        b->shutdown = (int)num;
        b->init = 1;
        break;
    case BIO_C_GET_FD:
        if (b->init) {
            ip = (int *)ptr;
            if (ip != NULL)
                *ip = b->num;
            ret = b->num;
        } else
            ret = -1;
        break;
    case BIO_CTRL_GET_CLOSE:
        ret = b->shutdown;
        break;
    case BIO_CTRL_SET_CLOSE:
        b->shutdown = (int)num;
        break;
    case BIO_CTRL_DUP:
    case BIO_CTRL_FLUSH:
        ret = 1;
        break;
    default:
        ret = 0;
        break;
    }
    return (ret);
}
