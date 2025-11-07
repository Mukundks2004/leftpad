import Leftpad.MksNat

namespace Leftpad.NatTheorems

open Leftpad.MksNat

/- Zero properties -/
theorem MyNat.add_zero (m : MyNat) : m.my_add MyNat.my_zero = m := by
  rfl

theorem MyNat.zero_add (m : MyNat) : MyNat.my_zero.my_add m = m := by
  induction m with
    | my_zero => rfl
    | my_succ n ih =>
      rw [MyNat.my_add, ih]

/- Addition properties -/
theorem MyNat.add_succ (m n : MyNat) : m.my_add n.my_succ = (m.my_add n).my_succ := by
  rfl

theorem MyNat.succ_add (m n : MyNat) : m.my_succ.my_add n = (m.my_add n).my_succ := by
  induction n with
  | my_zero => rfl
  | my_succ n ih =>
    rw [MyNat.add_succ, ih, MyNat.add_succ]

theorem MyNat.add_comm (m n : MyNat) : m.my_add n = n.my_add m := by
  induction m with
  | my_zero => rw [MyNat.zero_add, MyNat.add_zero]
  | my_succ m ih =>
    rw [MyNat.add_succ, MyNat.succ_add, ih]

/- Subtraction properties -/
theorem MyNat.zero_sub (m : MyNat) : MyNat.my_sub MyNat.my_zero m = MyNat.my_zero := by
  match m with
  | MyNat.my_zero => rfl
  | MyNat.my_succ _ => rfl

theorem MyNat.sub_zero (m : MyNat) : m.my_sub MyNat.my_zero = m := by
  match m with
  | MyNat.my_zero => rfl
  | MyNat.my_succ _ => rfl

theorem MyNat.succ_sub_succ (m n : MyNat) : m.my_succ.my_sub n.my_succ = m.my_sub n := by
  rfl

/- Max properties -/
theorem MyNat.zero_max (m : MyNat) : MyNat.my_zero.my_max m = m := by
  match m with
  | MyNat.my_zero => rfl
  | MyNat.my_succ _ => rfl

theorem MyNat.max_zero (m : MyNat) : m.my_max MyNat.my_zero = m := by
  match m with
  | MyNat.my_zero => rfl
  | MyNat.my_succ _ => rfl

theorem MyNat.succ_max_succ (m n : MyNat) : m.my_succ.my_max n.my_succ = (m.my_max n).my_succ := by
  rfl

theorem MyNat.max_comm (a b : MyNat) : MyNat.my_max a b = MyNat.my_max b a := by
  match a with
  | MyNat.my_zero => rw [MyNat.zero_max, MyNat.max_zero]
  | MyNat.my_succ a =>
    match b with
    | MyNat.my_zero => rw [MyNat.max_zero, MyNat.zero_max]
    | MyNat.my_succ b =>
      rw [MyNat.succ_max_succ, MyNat.succ_max_succ, MyNat.max_comm a b]

/- Combined properties -/
theorem MyNat.sub_add_eq_max (m n : MyNat) : (m.my_sub n).my_add n = m.my_max n := by
  match m, n with
  | MyNat.my_zero, _ => rw [MyNat.zero_sub, MyNat.zero_max, MyNat.zero_add]
  | _, MyNat.my_zero => rw [MyNat.sub_zero, MyNat.max_zero, MyNat.add_zero]
  | MyNat.my_succ m, MyNat.my_succ n =>
    rw [MyNat.succ_sub_succ, MyNat.succ_max_succ, MyNat.add_succ, MyNat.sub_add_eq_max m n]

theorem MyNat.add_sub_eq_max (m n : MyNat) : m.my_add (n.my_sub m) = m.my_max n := by
  rw [MyNat.add_comm, MyNat.max_comm, MyNat.sub_add_eq_max]

end Leftpad.NatTheorems
