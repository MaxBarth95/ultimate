//#Unsafe
/*
 * The relation x == 2 * i holds for the first 20 iterations, which is all the bounded unrollings that sample
 * loop-head states see, but not afterwards. Proposing it must not lead to a proof.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	int x = 0;
	while (i < 30) {
		i++;
		if (i <= 20) {
			x = x + 2;
		} else {
			x = x + 3;
		}
	}
	//@ assert x == 60;
}