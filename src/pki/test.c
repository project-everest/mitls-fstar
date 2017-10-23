#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "mipki.h"

void dump(const unsigned char *buffer, size_t len)
{
  int i;
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i]);
    if (i % 32 == 31 || i == len-1) printf("\n");
  }
}

int main(int argc, char **argv)
{
  mipki_config_entry config[1] = {
    {
      .cert_file = "../../data/server.crt",
      .key_file = "../../data/server.key",
      .is_universal = 0
    }
  };

  int erridx;
  mipki_state *st = mipki_init(config, 1, NULL, &erridx);

  if(!st)
  {
    printf("FAILURE: errid=%d\n", erridx);
    return 1;
  }

  printf("INIT OK\n");
  if(!mipki_add_root_file_or_path(st, "../../data/CAFile.pem"))
  {
    printf("Failed to add CAFile\n");
    return 1;
  }

  mipki_signature selected;
  mipki_signature offered[3] = {0x0403,0x0503,0x0401};

  mipki_chain s = mipki_select_certificate(st, "localhost", offered, 3, &selected);

  if(!s)
  {
    printf("Certificate selection failed.\n");
    return 1;
  }

  printf("Selected a certificate with signature=%04x\n", selected);

  if(!mipki_validate_chain(st, s, "localhost"))
    printf("Chain validation failed (expected, cert is self signed).\n");
  else
    printf("Chain validation OK.\n");

  char *tbs = "Hello World!";
  char *sig = malloc(8192);
  size_t sig_len = 8192;

  if(mipki_sign_verify(st, s, selected, tbs, strlen(tbs), sig, &sig_len, MIPKI_SIGN))
  {
    printf("Signature success <%04x, %s> (%d bytes):\n", selected, tbs, sig_len);
    dump(sig, sig_len);
    if(mipki_sign_verify(st, s, selected, tbs, strlen(tbs), sig, &sig_len, MIPKI_VERIFY))
    {
      printf("Signature verification suceeded.\n");
    }
    else
    {
      printf("Failed to verify signature!\n");
      return 1;
    }
  }
  else
  {
    printf("Failed to sign <%04x, %s>\n", selected, tbs);
    return 1;
  }

  size_t len = mipki_format_chain(st, s, sig, 8192);
  if(len > 0)
  {
    printf("Formatted chain:\n");
    dump(sig, len);
  }
  else{
    printf("ERROR: failed to format chain\n");
    return 1;
  }

  free(sig);

  return 0;
}
