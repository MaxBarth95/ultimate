//#Safe
/*
 * A loop with a nondeterministic bound; needs i <= n at the loop head.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int n = __VERIFIER_nondet_int();
	if (n < 0 || n > 1000000) {
		return 0;
	}
	int i = 0;
	while (i < n) {
		i++;
	}
	//@ assert i == n;
}