//#Safe
/*
 * x grows by 1 or 3 per iteration, so i <= x <= 3i at the loop head. Trace abstraction only ever refutes unwindings
 * through i here, so its interpolants say nothing about x; x <= 3i is a facet of the convex hull of the sampled
 * states (i, x).
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
		i++;
	}
	//@ assert x >= 1000 && x <= 3000;
}
