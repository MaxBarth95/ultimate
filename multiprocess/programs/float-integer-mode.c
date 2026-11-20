// The integer translation overapproximates float arithmetic, so the counterexample is feasible only with
// overapproximation: the coordinator must answer UNKNOWN, never FALSE (the bit-precise answer is FALSE).
extern void reach_error(void);
extern float __VERIFIER_nondet_float(void);
int main(void) {
  float a = __VERIFIER_nondet_float();
  float b = a + 1.0f;
  if (b == a) { reach_error(); }
  return 0;
}
