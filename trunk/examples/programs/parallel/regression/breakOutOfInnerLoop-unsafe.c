//#Unsafe
/*
 * An inner loop left by break, so the state after it is a waypoint: what is proven there for the paths that break
 * out must not be assumed for the path that leaves the loop normally.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
extern int __VERIFIER_nondet_int(void);

int main() {
	int i = 0;
	int k = 0;
	while (i < 3) {
		int j = 0;
		while (j < 5) {
			if (__VERIFIER_nondet_int()) {
				k = 1;
				break;
			}
			j++;
		}
		//@ assert k == 1 || j != 5 || i != 2;
		i++;
	}
}