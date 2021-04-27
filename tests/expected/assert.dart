compare_assert(int a, int b) {
  assert(a == b);
  assert(!(0 == 1));
}

main() {
  compare_assert(1, 1);
}
