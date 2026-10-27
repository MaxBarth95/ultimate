//#Safe
/*
 * Like twiceAtMost-safe.c with a counter that goes down: needs x + 2i <= 2000 at the loop head, the relation between
 * the series x <= 0, x <= 2, ... and i >= 1000, i >= 999, ... of the interpolants.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-27
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int i = 1000;
	int x = 0;
	while (i > 0) {
		if (__VERIFIER_nondet_int()) {
			x = x + 2;
		}
		i--;
	}
	//@ assert x <= 2000;
}
