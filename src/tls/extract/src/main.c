#include "TLSConstants.h"
#include "Test_TLSConstants.h"
int main() {
  FStar_Pervasives_Native_option__FStar_Pervasives_either__K___FStar_Bytes_bytes_Prims_string_Prims_string_K___FStar_Bytes_bytes_FStar_Bytes_bytes
    res =
    Test_TLSConstants_test_signatureSchemeListBytes();
    if (res.tag == FStar_Pervasives_Native_None) {
      printf ("ok\n");
      return 0;
    } else {
      if (res.val.case_Some.v.tag == FStar_Pervasives_Inl) {
        FStar_Bytes_bytes b =
          res.val.case_Some.v.val.case_Inl.v.fst;
        printf("Failed to parse back %d bytes : %s\n",
               b.length,
               FStar_Bytes_print_bytes(b));
        printf("\n%s, %s\n",
               res.val.case_Some.v.val.case_Inl.v.snd,
               res.val.case_Some.v.val.case_Inl.v.thd);
      } else {
        printf ("Failed to round trip\n");
        FStar_Bytes_bytes expected =
          res.val.case_Some.v.val.case_Inr.v.fst;
        FStar_Bytes_bytes got =
          res.val.case_Some.v.val.case_Inr.v.snd;
        printf("Expected: %s\nGot     : %s\nFailed!\n", 
               FStar_Bytes_print_bytes(expected),
               FStar_Bytes_print_bytes(got));
        return 1;
      }
    }
}
