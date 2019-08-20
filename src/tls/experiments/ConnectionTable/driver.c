#include "Test.h"

int main(){
  client_hello ch1 = {0, false};
  client_hello ch2 = {0, true};

  test(0, ch1, ch2);

  return 0;
}
