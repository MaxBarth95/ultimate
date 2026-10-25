//#Safe
/*
 * j stays five ahead of i; needs j == i + 5 && i <= 100000 at the loop head.
 * Author: Max Barth (max.barth@lmu.de)
 * Date: 2026-10-25
 */
int main() {
	int i = 0;
	int j = 5;
	while (i < 100000) {
		i++;
		j++;
	}
	//@ assert j == 100005;
}