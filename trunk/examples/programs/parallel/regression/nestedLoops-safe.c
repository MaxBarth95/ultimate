//#Safe
/*
 * Nested loops, each with an invariant at its own head.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	while (i < 1000) {
		int j = 0;
		while (j < 1000) {
			j++;
		}
		//@ assert j == 1000;
		i++;
	}
	//@ assert i == 1000;
}