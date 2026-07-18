#include "TLS13_Impl_Client_Driver.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

int main(void) {
  uint8_t server_name[] = "localhost";
  uint8_t empty_trust_anchors[1] = {0};
  TLS13_Impl_Client_Driver_client_driver created =
      TLS13_Impl_Client_Driver_new_client(
          server_name,
          strlen((const char *)server_name),
          empty_trust_anchors,
          0,
          0);
  (void)created;

  printf("extracted Pulse top-level driver API smoke test passed\n");
  return 0;
}
