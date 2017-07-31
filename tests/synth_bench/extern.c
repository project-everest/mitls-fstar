#include "types.h"

// A special extern function to make sure the negotationState is not optimized away.
void ns_live(negotationState ns) {
    return;
}
