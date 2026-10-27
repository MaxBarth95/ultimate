//#Unsafe
/*
 * Like parityCounter-safe.c, but from i = 40 on x grows by 2 at even i, so x <= 1 fails far beyond any small k.
 * Proposing the bounds of x must not lead to a proof.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-26
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int n = __VERIFIER_nondet_int();
	int i = 0;
	int x = 0;
	while (i < n) {
		if (i % 2 == 0) {
			if (i < 40) {
				x = x + 1;
			} else {
				x = x + 2;
			}
		} else {
			x = x - 1;
		}
		i++;
	}
	//@ assert x >= 0 && x <= 1;
}
