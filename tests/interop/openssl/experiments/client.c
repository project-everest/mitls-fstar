#include <stdio.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <string.h>
#include "openssl/ssl.h"
#include "openssl/err.h"

// #define HOST_NAME "www.random.org"
#define HOST_PORT 4433

// long res = 1;

// SSL_CTX* ctx = NULL;
// BIO *web = NULL, *out = NULL;
// SSL *ssl = NULL;

// init_openssl_library();


int connect_to_server( int port )
{
	int sock;
    struct sockaddr_in server;
    char message[1000] , server_reply[2000];
     
    //Create socket
    sock = socket(AF_INET , SOCK_STREAM , 0);
    if (sock == -1)
    {
        printf("Could not create socket");
    }

    server.sin_addr.s_addr = inet_addr("127.0.0.1");
    server.sin_family = AF_INET;
    server.sin_port = htons( port );

    //Connect to remote server
    printf("Trying to connect to port %d\n", port );
    if (connect(sock , (struct sockaddr *)&server , sizeof(server)) < 0)
    {
        perror("connect failed. Error");
        exit(EXIT_FAILURE);
    }

    return sock;
}

SSL_CTX *create_context()
{
    const SSL_METHOD *method;
    SSL_CTX *ctx;

    method = TLS_client_method();

    ctx = SSL_CTX_new(method);
    if (!ctx) {
		perror("Unable to create SSL context");
		// ERR_print_errors_fp(stderr);
		exit(EXIT_FAILURE);
    }

    return ctx;
}

void configure_context(SSL_CTX *ctx)
{
	if( 1 != SSL_CTX_set_min_proto_version( ctx, TLS1_3_VERSION ) ) {
        printf("Error at SSL_CTX_set_min_proto_version\n");
        exit(EXIT_FAILURE);
    }
    if( 1 != SSL_CTX_set_max_proto_version( ctx, TLS1_3_VERSION ) ) {
        printf("Error at SSL_CTX_set_min_proto_version\n");
        exit(EXIT_FAILURE);
    }

    if( 1 != SSL_CTX_set1_sigalgs_list( ctx, "ECDSA+SHA256" ) ){
        printf("Error at SSL_CTX_set1_sigalgs_list\n");
        exit(EXIT_FAILURE);
    }
	//SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, verify_callback);

}

int main(int argc, char **argv)
{
    int 		sock;
    SSL_CTX 	*ctx;
    SSL 		*ssl   = NULL;
    int 		result = -1;

    ctx = create_context();
    configure_context(ctx);

    sock = connect_to_server( HOST_PORT );
    ssl  = SSL_new(ctx);
   
    SSL_set_fd(ssl, sock);
    const char* availableCiphers = SSL_get_cipher_list( ssl, 0 );
    printf( "availableCiphers = %s\n", availableCiphers );

    if ( SSL_connect(ssl) != 1 ) {
    	printf("Error in SSL_connect\n" );
    	// ERR_print_errors_fp(stderr);
    	exit(1);
    }
    //X509* cert = SSL_get_peer_certificate(ssl);

    const char msg[] = "client->server\n";
    result = SSL_write(ssl, msg, strlen(msg));
    if( result <= 0 ) {
    	printf("SSL_read --> %d\n", result );
    	// ERR_print_errors_fp(stderr);
    	exit(1);
    }

    char buff[ 100 ] = {0};
    int errorCode = SSL_ERROR_WANT_READ;
    while( errorCode == SSL_ERROR_WANT_READ ) {
    	result = SSL_read( ssl, buff, sizeof( buff ) );	
    	if( result > 0 ) break;

    	errorCode = SSL_get_error( ssl, result);
    }
    
    printf("Server replied with: %s\n", buff);

    SSL_free(ssl);
	close( sock );
	// X509_free(cert);
	SSL_CTX_free( ctx );

	return 0;
}




// ctx = SSL_CTX_new(method);
// if(!(ctx != NULL)) handleFailure();

// /* Cannot fail ??? */
// SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, verify_callback);

// /* Cannot fail ??? */
// SSL_CTX_set_verify_depth(ctx, 4);

// /* Cannot fail ??? */
// const long flags = SSL_OP_NO_SSLv2 | SSL_OP_NO_SSLv3 | SSL_OP_NO_COMPRESSION;
// SSL_CTX_set_options(ctx, flags);

// res = SSL_CTX_load_verify_locations(ctx, "random-org-chain.pem", NULL);
// if(!(1 == res)) handleFailure();

// web = BIO_new_ssl_connect(ctx);
// if(!(web != NULL)) handleFailure();

// res = BIO_set_conn_hostname(web, HOST_NAME ":" HOST_PORT);
// if(!(1 == res)) handleFailure();

// BIO_get_ssl(web, &ssl);
// if(!(ssl != NULL)) handleFailure();

// const char* const PREFERRED_CIPHERS = "HIGH:!aNULL:!kRSA:!PSK:!SRP:!MD5:!RC4";
// res = SSL_set_cipher_list(ssl, PREFERRED_CIPHERS);
// if(!(1 == res)) handleFailure();

// res = SSL_set_tlsext_host_name(ssl, HOST_NAME);
// if(!(1 == res)) handleFailure();

// out = BIO_new_fp(stdout, BIO_NOCLOSE);
// if(!(NULL != out)) handleFailure();

// res = BIO_do_connect(web);
// if(!(1 == res)) handleFailure();

// res = BIO_do_handshake(web);
// if(!(1 == res)) handleFailure();

// /* Step 1: verify a server certificate was presented during the negotiation */
// X509* cert = SSL_get_peer_certificate(ssl);
// if(cert) { X509_free(cert); } /* Free immediately */
// if(NULL == cert) handleFailure();

// /* Step 2: verify the result of chain verification */
// /* Verification performed according to RFC 4158    */
// res = SSL_get_verify_result(ssl);
// if(!(X509_V_OK == res)) handleFailure();

// /* Step 3: hostname verification */
// /* An exercise left to the reader */

// BIO_puts(web, "GET " HOST_RESOURCE " HTTP/1.1\r\n"
//               "Host: " HOST_NAME "\r\n"
//               "Connection: close\r\n\r\n");
// BIO_puts(out, "\n");

// int len = 0;
// do
// {
//   char buff[1536] = {};
//   len = BIO_read(web, buff, sizeof(buff));
            
//   if(len > 0)
//     BIO_write(out, buff, len);

// } while (len > 0 || BIO_should_retry(web));

// if(out)
//   BIO_free(out);

// if(web != NULL)
//   BIO_free_all(web);

// if(NULL != ctx)
//   SSL_CTX_free(ctx);