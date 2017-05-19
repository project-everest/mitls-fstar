#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#if _WIN32 // Windows 32-bit or 64-bit... mingw
#include <winsock2.h>
#else
#include <sys/socket.h>
typedef SOCKET int;
#define SOCKET_ERROR (-1)
#define WSAGetLastError() (errno)
#define closesocket(fd) close(fd)
#endif
#include <mitlsffi.h>

const char *option_hostname;
int option_port;

#define OPTION_LIST \
	STRING_OPTION("-v", version, "sets maximum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.3)") \
	STRING_OPTION("-mv", minversion, "sets minimum protocol version to <1.0 | 1.1 | 1.2 | 1.3> (default: 1.2)") \
	BOOL_OPTION("-s", isserver, "run as server instead of client") \
	BOOL_OPTION("-0rtt", 0rtt, "enable early data (server support and client offer)") \
	STRING_OPTION("-psk", psk, "L:K add an entry in the PSK database at label L with key K (in hex), associtated with the fist current -cipher") \
	STRING_OPTION("-offerpsk", offerpsk, "offer the given PSK identifier(s) (must be loaded first with --psk). Client only.") \
	BOOL_OPTION("-verify", verify, "enforce peer certificate validation") \
	BOOL_OPTION("-noems", noems, "disable extended master secret in TLS <= 1.2 (client only)") \
    STRING_OPTION("-ciphers", ciphers, "colon-separated list of cipher suites; see above for valid values") \
    STRING_OPTION("-sigalgs", sigalgs, "colon-separated list of signature algorithms; see above for valid values") \
    STRING_OPTION("-groups", groups, "colon-separated list of named groups; see above for valid values") \
    STRING_OPTION("-cert", cert, "PEM file containing certificate chain to send") \
    STRING_OPTION("-key", key, "PEM file containing private key of endpoint certificate in chain") \
    STRING_OPTION("-CAFile", cafile, "set openssl root cert file to <path>")

// Declare global variables representing the options	
#define STRING_OPTION(n, var, help) const char *option_##var;
#define BOOL_OPTION(n, var, help)   int option_##var;
OPTION_LIST
#undef STRING_OPTION
#undef BOOL_OPTION

// Fill in a datastructure describing the options
#define STRING_OPTION(n, var, help) { n, &option_##var, NULL, help },
#define BOOL_OPTION(n, var, help)   { n, NULL, &option_##var, help },
struct {
	const char *OptionName;		// name of the option switch
	const char **String;		// place to store the option argument string, or NULL if no argument follows
	int *Boolean;				// if String==NULL, then this is the place to store a boolean '1'
	const char *HelpText;		// help text for the option
} Options[] = {
	OPTION_LIST
	{}
};
#undef STRING_OPTION
#undef BOOL_OPTION

typedef struct {
  struct _FFI_mitls_callbacks cb;
  SOCKET sockfd;
} callback_context;

// Print the usage text
void PrintUsage(void)
{
	size_t i=0;

    printf("Usage:  cmitls.exe [options] hostname port\n");	
	for (i=0; Options[i].OptionName; ++i) {
		printf("  %-10s %s\n", Options[i].OptionName, Options[i].HelpText);
	}
}

const char *hostname_arg;
const char *port_arg;

// Parse one argument, prefixed by "-"
//  Name - the argument name, including the "-"
//  ArgsRemaining - the number of elements in argvRemaining
//  argvRemaining - the remaining arguments
//
// Returns -1 for failure, or 1 or 2, to report the number 
// of arguments consumed
int ParseArg(const char *Name, int ArgsRemaining, char **argvRemaining)
{
	size_t i=0;
	
	for (i=0; Options[i].OptionName; ++i) {
		if (strcmp(Options[i].OptionName, Name) == 0) {
			if (Options[i].String) {
				if (ArgsRemaining) {
					*(Options[i].String) = argvRemaining[0];
				} else {
					return -1;
				}
				return 2;
			} else {
				*(Options[i].Boolean) = 1;
				return 1;
			}
		}
	}
	printf("Unknown option: %s\n", Name);
	return -1; // Unknown option
}

// Parse the command line arguments
// Returns -1 for failure, 0 for success
int ParseArgs(int argc, char **argv)
{
	int i = 1;
	int result;
	
	while (i < argc) {
		if (argv[i][0] == '-') {
			result = ParseArg(argv[i], argc-i-1, &argv[i+1]);
			if (result == -1) {
				return -1;
			}
			i += result;
		} else if (hostname_arg == NULL) {
			hostname_arg = argv[i++];
		} else if (port_arg == NULL) {
			port_arg = argv[i++];
		} else {
			printf("Unknown argument: %s\n", argv[i]);
			return -1;
		}
	}
	
	if (hostname_arg) {
		option_hostname = hostname_arg;
	} else {
		option_hostname = (option_isserver) ? "0.0.0.0" : "127.0.0.1";
	}
	if (port_arg) {
		option_port = atoi(port_arg);
	} else {
		option_port = 443;
	}
	return 0;
}

void PrintErrors(char *out_msg, char *err_msg)
{
	if (out_msg) {
		printf("MITLS: %s", out_msg);
		FFI_mitls_free_msg(out_msg);
	}
	if (err_msg) {
		fprintf(stderr, "MITLS: %s", err_msg);
		FFI_mitls_free_msg(err_msg);
	}
}

int Configure(mitls_state **pstate)
{
	char *out_msg;
	char *err_msg;
	mitls_state *state;
	int r;
	
	*pstate = NULL;
	
	r = FFI_mitls_configure(&state, option_version, option_hostname, &out_msg, &err_msg);
	PrintErrors(out_msg, err_msg);
	if (r == 0) {
		printf("FFI_mitls_configure(%s,%s) failed.\n", option_version, option_hostname);
		return 2;
	}
	if (option_cert) {
		r = FFI_mitls_configure_cert_chain_file(state, option_cert);
		if (r == 0) {
			printf("FFI_mitls_configure_cert_chain_file(%s) failed.\n", option_cert);
			return 2;
		}
	}
	if (option_key) {
		r = FFI_mitls_configure_private_key_file(state, option_key);
		if (r == 0) {
			printf("FFI_mitls_configure_private_key_file(%s) failed.\n", option_key);
			return 2;
		}
	}
	if (option_cafile) {
		r = FFI_mitls_configure_ca_file(state, option_cafile);
		if (r == 0) {
			printf("FFI_mitls_configure_ca_file(%s) failed.\n", option_cafile);
			return 2;
		}
	}
	if (option_ciphers) {
		r = FFI_mitls_configure_cipher_suites(state, option_ciphers);
		if (r == 0) {
			printf("FFI_mitls_configure_cipher_suites(%s) failed.\n", option_ciphers);
			return 2;
		}
	}
	if (option_sigalgs) {
		r = FFI_mitls_configure_signature_algorithms(state, option_sigalgs);
		if (r == 0) {
			printf("FFI_mitls_configure_signature_algorithms(%s) failed.\n", option_sigalgs);
			return 2;
		}
	}
	if (option_groups) {
		r = FFI_mitls_configure_named_groups(state, option_groups);
		if (r == 0) {
			printf("FFI_mitls_configure_named_groups(%s) failed.\n", option_groups);
			return 2;
		}
	}
	*pstate = state;
	return 0;
}

// Callback from miTLS, when it is ready to send a message via the socket
int SendCallback(struct _FFI_mitls_callbacks *callbacks, const void *buffer, size_t buffer_size)
{
	callback_context *ctx = (callback_context*)callbacks;
	ssize_t r;
	
	r = send(ctx->sockfd, buffer, buffer_size, 0);
	if (r != buffer_size) {
		printf("Error %d returned from socket send()\n", WSAGetLastError());
	}
	return (int)r;
}

// Callback from miTLS, when it is ready to receive a message via the socket
int RecvCallback(struct _FFI_mitls_callbacks *callbacks, void *buffer, size_t buffer_size)
{
	callback_context *ctx = (callback_context*)callbacks;
	ssize_t r;
	
	r = recv(ctx->sockfd, buffer, buffer_size, 0);
	if (r != buffer_size) {
		printf("Error %d returned from socket recv()\n", WSAGetLastError());
	}
	return (int)r;
}

#define MAX_RECEIVED_REQUEST_LENGTH  (65536) // 64kb
int SingleServer(mitls_state *state, SOCKET clientfd)
{
	callback_context ctx;
	char *out_msg;
	char *err_msg;
	void *db;
	size_t db_length;
	int r;
	size_t payload_length;
	char *payload;
	
	const char ctext[] = "You are connected to miTLS*!\r\n"
                         "This is the request you sent:\r\n\r\n";	
    const char cpayload[] = "HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length:%d\r\n"
	                        "Content-Type: text/plain; charset=utf-8\r\n\r\n";
		
	ctx.cb.send = SendCallback;
	ctx.cb.recv = RecvCallback;
	ctx.sockfd = clientfd;
	r = FFI_mitls_accept_connected(&ctx.cb, state, &out_msg, &err_msg);
	PrintErrors(out_msg, err_msg);
	if (r == 0) {
		printf("FFI_mitls_accept_connected() failed\n");
		return 1;
	}
	db = FFI_mitls_receive(state, &db_length, &out_msg, &err_msg);
	if (db == NULL) {
		printf("FFI_mitls_receive() failed\n");
		return 1;
	}
	printf("Received data:\n");
	puts((const char *)db);
	
	// Truncate overly long client requests
	if (db_length > MAX_RECEIVED_REQUEST_LENGTH) {
		db_length = MAX_RECEIVED_REQUEST_LENGTH;
	}
	
	// Determine the payload length.  This length is the maximum... the actual
	// length may be a few bytes less due to differing db_length-to-string conversions.
	// +5 for the number of characters needed to render text for the max db_length of 65536.
	payload_length=sizeof(ctext) + sizeof(cpayload) + db_length + 5;
	payload = (char*)_alloca(payload_length);
	sprintf(payload, cpayload, (int)(sizeof(ctext)+db_length-1) /* not counting the '\0' at the end of ctext */);
	strcat(payload, ctext);
	strncat(payload, (const char*)db, db_length);

	FFI_mitls_free_msg(db);
	
	r = FFI_mitls_send(state, payload, strlen(payload), &out_msg, &err_msg);
	PrintErrors(out_msg, err_msg);
	if (r == 0) {
		printf("FFI_mitls_send() failed\n");
		return 1;
	}
	FFI_mitls_close(state);
	return 0;
}

int TestServer()
{
	UINT_PTR sockfd;
	struct hostent *host;
	struct sockaddr_in addr;
	mitls_state *state;
	
	printf("===============================================\n Starting test TLS server...\n");
	
	host = gethostbyname(option_hostname);
	if (host == NULL) {
		printf("Failed gethostbyname(%s) %d\n", option_hostname, WSAGetLastError());
		return 1;
	}
	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	memcpy(&addr.sin_addr.s_addr, host->h_addr, host->h_length);
	addr.sin_port = htons(option_port);	
	
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	if (sockfd < 0) {
		printf("Failed socket open: %d\n", WSAGetLastError());
		return 1;
	}
	if (bind(sockfd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
		printf("Failed bind() %d\n", WSAGetLastError());
		closesocket(sockfd);
		return 1;
	}
	if (listen(sockfd, 128) < 0) {
		printf("Failed listen() %d\n", WSAGetLastError());
		closesocket(sockfd);
		return 1;
	}
	while (1) {
		UINT_PTR clientsockfd;
		int len = sizeof(addr);
		
		clientsockfd = accept(sockfd, (struct sockaddr*)&addr, &len);
		if (clientsockfd == SOCKET_ERROR) {
			printf("Failed accept() %d\n", WSAGetLastError());
			closesocket(sockfd);
			return 1;
		}
		if (Configure(&state) != 0) {
			return 1;
		}
		if (SingleServer(state, clientsockfd)) {
			return 1;
		}
		closesocket(clientsockfd);
	}
	return 0;
}

int TestClient(void)
{
	mitls_state *state;
	UINT_PTR sockfd;
	struct hostent *peer;
	struct sockaddr_in addr;
	int requestlength;
	ssize_t r;
	callback_context ctx;
	char *out_msg;
	char *err_msg;
	char request[512];
	void *response;
	size_t response_length;

	printf("===============================================\n");
	printf("Starting test client...\n");
	
	const char request_template[] = "GET / HTTP/1.1\r\nHost: %s\r\n\r\n";
	if (sizeof(request_template) + strlen(option_hostname) >= sizeof(request)) {
		// Host name is too long
		printf("Host name is too long.\n");
		return 1;
	}
	requestlength = sprintf(request, request_template, option_hostname);
	
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	if (sockfd < 0) {
		printf("Failed socket open: %s\n", strerror(errno));
		return 1;
	}
	peer = gethostbyname(option_hostname);
	if (peer == NULL) {
		printf("Failed gethostbyname %s\n", strerror(errno));
		return 1;
	}
	memset(&addr, 0, sizeof(addr));
	addr.sin_family = AF_INET;
	memcpy(&addr.sin_addr.s_addr, peer->h_addr, peer->h_length);
	addr.sin_port = htons(option_port);
	
	if (connect(sockfd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
		printf("Failed connect %s\n", strerror(errno));
		return 1;
	}

	r = Configure(&state);
	if (r != 0) {
		return 1;
	}
	
	ctx.cb.send = SendCallback;
	ctx.cb.recv = RecvCallback;
	ctx.sockfd = sockfd;
	r = FFI_mitls_connect(&ctx.cb, state, &out_msg, &err_msg);
	PrintErrors(out_msg, err_msg);
	if (r == 0) {
		printf("FFI_mitls_connect() failed\n");
		return 1;
	}
	
	printf("Read OK, sending HTTP request...\n");
	r = FFI_mitls_send(state, request, requestlength, &out_msg, &err_msg);
	PrintErrors(out_msg, err_msg);
	if (r == 0) {
		printf("FFI_mitls_send() failed\n");
		closesocket(sockfd);
		return 1;
	}
	
	response = FFI_mitls_receive(state, &response_length, &out_msg, &err_msg);
	if (response == NULL) {
		printf("FFI_mitls_receive() failed\n");
		closesocket(sockfd);
		return 1;
	}
	printf("Received data:\n");
	puts((const char *)response);
	FFI_mitls_free_msg(response);
	
	printf("Closing connection, irrespective of the response\n");
	FFI_mitls_close(state);
	closesocket(sockfd);
	
	return 0;
}

int main(int argc, char **argv)
{
	int r;
	
#if _WIN32
{
	WSADATA wsaData;
	r = WSAStartup(MAKEWORD(2,2), &wsaData);
	if (r != 0) {
		printf("WSAStartup failed: %d\n", r);
		return 2;
	}
}
#endif	
	
	option_version = "1.3";
	if (ParseArgs(argc, argv) != 0) {
		PrintUsage();
		return 1;
	}

	if (option_minversion) {
		printf("Warning: -mv is not supported via FFI yet.  Ignored.\n");
	}
	
	r = FFI_mitls_init();
	if (r == 0) {
		printf("FFI_mitls_init() failed!\n");
		return 2;
	}
	
	if (option_isserver) {
		r = TestServer();
	} else {
		r = TestClient();
	}
	FFI_mitls_cleanup();

	return r;
}