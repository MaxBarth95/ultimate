//#Unsafe
/*
 * The bug is reached in the fourth iteration. An invariant that is assumed although it does not hold everywhere
 * would hide it.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	while (i < 10) {
		i++;
		//@ assert i != 4;
	}
}