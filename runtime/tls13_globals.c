/* Custard's C backend assigns the globals that C cannot initialize statically
   in custard_init_globals(), which the embedding program must call before
   using the library.  Linked with every build of the full library, so the
   call happens at load time. */
#include "TLS13.h"

__attribute__((constructor)) static void tls13_init_globals(void) {
  custard_init_globals();
}
