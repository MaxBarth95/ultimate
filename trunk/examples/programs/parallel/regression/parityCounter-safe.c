//#Safe
/*
 * x flips between 0 and 1 with the parity of i. The bounds 0 <= x <= 1 are not inductive (x = 1 at an even i goes
 * to 2), but 2-inductive; x == i % 2 is not affine, so the samples give no equality.
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
			x = x + 1;
		} else {
			x = x - 1;
		}
		i++;
	}
	//@ assert x >= 0 && x <= 1;
}
