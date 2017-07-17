#include <stdio.h>
#include <unistd.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <string.h>
#include "openssl/ssl.h"
#include "openssl/err.h"


int create_socket(int port)
{
    int s;
    struct sockaddr_in addr;

    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    addr.sin_addr.s_addr = htonl(INADDR_ANY);

    s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0) {
	perror("Unable to create socekt");
	exit(EXIT_FAILURE);
    }

    if (bind(s, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
	perror("Unable to bind");
	exit(EXIT_FAILURE);
    }

    if (listen(s, 1) < 0) {
	perror("Unable to listen");
	exit(EXIT_FAILURE);
    }
    printf("Listenning on port %d\n", port );

    return s;
}

SSL_CTX *create_context()
{
    const SSL_METHOD *method;
    SSL_CTX *ctx;

    method = TLS_server_method();

    ctx = SSL_CTX_new(method);
    if (!ctx) {
    	perror("Unable to create SSL context");
    	exit(EXIT_FAILURE);
    }

    if( 1 != SSL_CTX_set_min_proto_version( ctx, TLS1_3_VERSION ) ) {
        printf("Error at SSL_CTX_set_min_proto_version\n");
        exit(EXIT_FAILURE);
    }
    if( 1 != SSL_CTX_set_max_proto_version( ctx, TLS1_3_VERSION ) ) {
        printf("Error at SSL_CTX_set_max_proto_version\n");
        exit(EXIT_FAILURE);
    }

    if( 1 != SSL_CTX_set1_sigalgs_list( ctx, "ECDSA+SHA256" ) ){
        printf("Error at SSL_CTX_set1_sigalgs_list\n");
        exit(EXIT_FAILURE);
    }

    return ctx;
}

void configure_context(SSL_CTX *ctx)
{
    const char* SERVER_KEY_PATH             = "../../../../../everest/mitls-fstar/data/server-ecdsa.key";
    // const char* SERVER_CA_PATH              = "../../../../../everest/mitls-fstar/data/ca.crt";
    const char* SERVER_CERT_PATH            = "../../../../../everest/mitls-fstar/data/server-ecdsa.crt" ;

    /* Set the key and cert */
    if (SSL_CTX_use_certificate_file(ctx, SERVER_CERT_PATH, SSL_FILETYPE_PEM) != 1) {
        ERR_print_errors_fp(stderr);
	   exit(EXIT_FAILURE);
    }

    if (SSL_CTX_use_PrivateKey_file(ctx, SERVER_KEY_PATH, SSL_FILETYPE_PEM) != 1 ) {
        ERR_print_errors_fp(stderr);
	   exit(EXIT_FAILURE);
    }
}

int main(int argc, char **argv)
{
    int sock;
    SSL_CTX *ctx;
    int result = -1;

    // init_openssl();
    ctx = create_context();

    configure_context(ctx);

    sock = create_socket(4433);

    printf("Starting server\n");
    /* Handle connections */
    while(1) {
        struct sockaddr_in addr;
        uint len = sizeof(addr);
        SSL *ssl;
        const char reply[] = "test\n";

        int client = accept(sock, (struct sockaddr*)&addr, &len);
        if (client < 0) {
            perror("Unable to accept");
            exit(EXIT_FAILURE);
        }

        ssl = SSL_new(ctx);
        SSL_set_fd(ssl, client);

        const char* availableCiphers = SSL_get_cipher_list( ssl, 0 );
        printf( "availableCiphers = %s\n", availableCiphers );

        if (SSL_accept(ssl) <= 0) {
            ERR_print_errors_fp(stderr);
            exit(EXIT_FAILURE);
        }
    

        char buff[ 100 ] = {0};
        result = SSL_read( ssl, buff, sizeof( buff ) );
        if( result <= 0 ) {
            printf("SSL_read --> %d\n", result );
            // ERR_print_errors_fp(stderr);
            exit(1);
        }
        else {
            printf("Client sent: %s\n", buff);
        }
        
        result = SSL_write(ssl, reply, strlen(reply));
        printf("SSL_write --> %d\n", result );
        if( result <= 0 ) {
            // ERR_print_errors_fp(stderr);
            exit(1);
        }

        SSL_free(ssl);
        close(client);
    }

    close(sock);
    SSL_CTX_free(ctx);
    printf("exiting server\n");
    // cleanup_openssl();
}