//#Safe
/*
 * A loop whose assertion needs the invariant x == 2 * i && i <= 100000 at the loop head.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	int x = 0;
	while (i < 100000) {
		i++;
		x = x + 2;
	}
	//@ assert x == 200000;
}