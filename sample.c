typedef unsigned int u32;

u32 const6() {
  return 6U;
}

u32 var6() {
  u32 x = 6;
  return x;
}

u32 sum6_simple() {
  u32 x = 4;
  u32 y = 2;
  return x + y;
}

u32 sum6_hard() {
  u32 x = 3;
  u32 y = 2;
  u32 z = 1;
  u32 retval = x + y + z;
  return retval;
}

u32 shiftl6() {
  u32 x = 3;
  return x << 1;
}

u32 shiftr6() {
  u32 x = 12;
  return x >> 1;
}

u32 sum6_loop() {
  u32 x = 0;
  for(u32 i = 0; i <4; ++i)
    x = x + i;
  return x;
}

u32 sign(int x) {
  return x >> 31;
}

u32 oppositesign(int x) {
  return 1 - (x >> 31);
}

int main() {
  const6();
  var6();
  sign(-1);
  sign(1);
  oppositesign(-1);
  oppositesign(1);
  return 0;
}
