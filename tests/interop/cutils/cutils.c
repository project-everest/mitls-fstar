#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

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
	printf("########## %s in %s: %d; size = %d, source = %s \n", __FILE__, __FUNCTION__, __LINE__, size, source	 );
	char *dest = malloc( size );
	
	if( NULL == dest )
		return NULL;

	memcpy( dest, source, size );
	printf("########## %s in %s: %d; dest = %s \n", __FILE__, __FUNCTION__, __LINE__, dest	 );
	return dest;
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
	printf("########## %s in %s: %d; dest = %p; src = %p; size = %d\n", __FILE__, __FUNCTION__, __LINE__, dest, src, size );
	return memcpy( dest, src, size );
}