//#Unsafe
/*
 * The loop computes x == 10, which the assertion after the loop rules out.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	int x = 0;
	while (i < 5) {
		i++;
		x = x + 2;
	}
	//@ assert x != 10;
}