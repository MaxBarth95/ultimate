// #Safe: the reach_error() after the longjmp is dead code. The IcfgBuilder removes its error location from the
// program points but keeps it among the error locations; the program package must keep it too (the writer threw
// before it did).
extern void reach_error(void);
extern int setjmp(jmp_buf env);
extern void longjmp(jmp_buf env, int val);

jmp_buf env;
int global = 0;

void g(int x) {
  global = x;
  longjmp(env, 3);
  reach_error();
}

int main(void) {
  int val = setjmp(env);
  if (val == 0) {
    g(2);
    reach_error();
  }
  if (val != 3 || global != 2) {
    reach_error();
  }
  return 0;
}
