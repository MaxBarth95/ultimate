// #Safe: the loop keeps x <= n
extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = 0;
  int n = __VERIFIER_nondet_int();
  if (n < 0) return 0;
  while (x < n) { x = x + 1; }
  if (x > n) { reach_error(); }
  return 0;
}
