// With SMTInterpol alone the trace check of this nonlinear counterexample answers UNKNOWN (rule 3 of R2.6).
extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int z = __VERIFIER_nondet_int();
  if (x > 0 && y > 0 && z > 0 && x < 1000 && y < 1000 && z < 1000) {
    if (x * x * x + y * y * y == z * z * z) { reach_error(); }
  }
  return 0;
}
