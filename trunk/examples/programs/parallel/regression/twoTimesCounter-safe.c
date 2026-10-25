//#Safe
/*
 * x grows twice as fast as i up to a nondeterministic bound; needs x == 2 * i && i <= n at the loop head.
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
	int x = 0;
	while (i < n) {
		i++;
		x = x + 2;
	}
	//@ assert x == 2 * n;
}