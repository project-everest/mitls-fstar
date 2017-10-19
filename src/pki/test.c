#include <stdio.h>
#include <stdint.h>
#include "mipki.h"

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

  if(!mipki_init(config, 1, NULL, &erridx))
  {
    printf("FAILURE: errid=%d\n", erridx);
    return 1;
  }
  printf("INIT OK\n");
  return 0;
}
