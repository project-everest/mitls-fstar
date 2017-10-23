#include "TLSConstants.h"
#include "Test_TLSConstants.h"
int main() {
    K___Prims_list__TLSConstants_signatureScheme__FStar_Bytes_bytes x =
      Test_TLSConstants_test_signatureSchemeListBytes();
    for (unsigned int i = 0; i < x.snd.length; i++) {
      printf("%x", x.snd.data[i]);
    }
    printf("\n");
    return 0;
}
