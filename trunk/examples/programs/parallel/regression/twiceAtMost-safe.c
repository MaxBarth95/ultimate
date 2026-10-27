//#Safe
/*
 * x grows by 0 or 2 per iteration, so x <= 2i at the loop head, which trace abstraction does not find: its
 * interpolants at the successive visits of the loop head are x <= 0, x <= 2, x <= 4, ... on one trace and i <= 0,
 * i <= 1, i <= 2, ... on another. The interpolant shapes of the invariant supplier relate the two series.
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
		i++;
	}
	//@ assert x <= 2000;
}
