int a;
short b;
unsigned char c;
void d(char e) { a = e; }
int main(void) {
  b = ~c;
  d(b >> 8);
  return a;
}
