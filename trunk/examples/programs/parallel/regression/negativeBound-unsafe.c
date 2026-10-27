//#Unsafe
/*
 * Fails if n < 0: the loop is not entered and the program ends after the first visit of the loop head. The condition
 * of the loop proposes i <= n, which holds at every later visit; a base case of k-induction that only looks at
 * executions with k - 1 steps would miss the counterexample.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-26
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int n = __VERIFIER_nondet_int();
	int i = 0;
	while (i < n) {
		i++;
	}
	//@ assert i == n;
}
