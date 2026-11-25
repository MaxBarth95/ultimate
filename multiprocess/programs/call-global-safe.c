// #Safe: the callee modifies a global; in package mode the call's summary edge must not become a shortcut that
// havocs g (it gave an unsound FALSE before the writer left it out)
extern void reach_error(void);
int g;
void inc(void) { g = g + 1; }
int main(void) {
  g = 0;
  inc();
  inc();
  if (g != 2) { reach_error(); }
  return 0;
}
