//#Unsafe
/*
 * Like threeOrOne-safe.c, but x may grow by 4 in the third iteration, so x <= 3i is no invariant and the assertion
 * fails if it does.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-27
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int i = 0;
	int x = 0;
	while (i < 1000) {
		if (__VERIFIER_nondet_int()) {
			x = x + 3;
		} else {
			x = x + 1;
		}
		if (i == 2 && __VERIFIER_nondet_int()) {
			x = x + 1;
		}
		i++;
		//@ assert x <= 3 * i;
	}
}
