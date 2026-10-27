//#Safe
/*
 * x cycles through 0, 1, 2 with i % 3. The bounds 0 <= x <= 2 are 3-inductive, not inductive or 2-inductive, and
 * x is no affine function of i.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-26
 */
int main() {
	int i = 0;
	int x = 0;
	while (i < 100000) {
		if (i % 3 == 2) {
			x = x - 2;
		} else {
			x = x + 1;
		}
		i++;
	}
	//@ assert x >= 0 && x <= 2;
}
