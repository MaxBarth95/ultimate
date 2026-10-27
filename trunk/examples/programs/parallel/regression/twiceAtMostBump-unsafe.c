//#Unsafe
/*
 * Like twiceAtMost-safe.c, but x gets one more in the fourth iteration, so x <= 2i is no invariant and the assertion
 * fails if x grows in each of the first four iterations.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-27
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int i = 0;
	int x = 0;
	while (i < 1000) {
		if (__VERIFIER_nondet_int()) {
			x = x + 2;
		}
		if (i == 3) {
			x = x + 1;
		}
		i++;
		//@ assert x <= 2 * i;
	}
}
