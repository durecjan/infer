/* Atlas test: store and load of non-pointer local variable
   Expected: pure constraint (var == value) added,
   no spatial predicates involved, no dereference */

void store_load_int() {
    int x = 10;
    int y = x;
}
