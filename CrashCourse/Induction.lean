import CrashCourse.TypeClass


-- example (n : MyNat) : 0 + n = n := by
--   fail_if_success
--   sorry

#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

theorem MyNat.add_succ (m n : MyNat) : m + MyNat.succ n = MyNat.succ (m + n) := by
  rfl

theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n

  case zero =>
    rfl

  case succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]


set_option pp.fieldNotation.generalized false in

example (n : MyNat) : 0 + n = n := by
  induction n

  case zero =>
    rfl

  case succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]

example (n : MyNat) : 1 + n = MyNat.succ n := by
  induction n

  case zero =>
    rfl

  case succ n' iht =>
    rw [MyNat.add_succ]
    rw [iht]
