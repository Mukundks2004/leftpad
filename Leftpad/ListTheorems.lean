import Leftpad.BoolTheorems
import Leftpad.MksBool
import Leftpad.MksList
import Leftpad.MksNat
import Leftpad.NatTheorems

namespace Leftpad.ListTheorems

open Leftpad.BoolTheorems
open Leftpad.MksBool
open Leftpad.MksList
open Leftpad.MksNat
open Leftpad.NatTheorems

/- Append Theorems -/
theorem MyList.cons_append {α : Type} (x : α) (xs ys : MyList α) : (MyList.my_cons x xs).my_append ys = MyList.my_cons x (xs.my_append ys) := by
  rfl

theorem MyList.nil_append {α : Type} (xs : MyList α) : MyList.my_nil.my_append xs = xs := by
  rfl

theorem MyList.append_nil {α : Type} (xs : MyList α) : xs.my_append MyList.my_nil = xs := by
  match xs with
  | MyList.my_nil => rfl
  | MyList.my_cons x xs =>
    rw [MyList.cons_append, MyList.append_nil]

theorem MyList.append_assoc {α : Type} (xs ys zs : MyList α) : xs.my_append (ys.my_append zs)  = (xs.my_append ys).my_append zs := by
  match xs with
  | MyList.my_nil => rfl
  | MyList.my_cons x xs =>
    rw [MyList.cons_append, MyList.cons_append, MyList.cons_append, MyList.append_assoc xs ys zs]

/- Length Theorems -/
theorem MyList.nil_length {α : Type} : (MyList.my_nil : MyList α).my_length = MyNat.my_zero := by
  rfl

theorem MyList.cons_length {α : Type} (x : α) (xs : MyList α) : (MyList.my_cons x xs).my_length = xs.my_length.my_succ := by
  rfl

theorem MyList.append_length {α : Type} (xs ys : MyList α) : (xs.my_append ys).my_length = xs.my_length.my_add ys.my_length := by
  induction xs with
  | my_nil =>
    rw [MyList.nil_append, MyList.nil_length, MyNat.zero_add]
  | my_cons _ _ ih =>
    rw [MyList.cons_length, MyList.cons_append, MyList.cons_length, ih, MyNat.succ_add]

/- Reverse Theorems -/
theorem MyList.reverse_nil {α : Type} : MyList.my_reverse (MyList.my_nil : MyList α) = MyList.my_nil := by
  rfl

theorem MyList.cons_reverse {α : Type} (x : α) (xs : MyList α) : (MyList.my_cons x xs).my_reverse = xs.my_reverse.my_append (MyList.my_cons x MyList.my_nil) := by
  rfl

theorem MyList.append_reverse {α : Type} (xs ys : MyList α) : (xs.my_append ys).my_reverse = ys.my_reverse.my_append xs.my_reverse := by
  induction xs with
  | my_nil =>
    rw [MyList.nil_append, MyList.reverse_nil, MyList.append_nil]
  | my_cons _ _ ih =>
    rw [MyList.cons_append, MyList.cons_reverse, MyList.cons_reverse, MyList.append_assoc, ih]

/- Suffix and Prefix Theorems -/
theorem MyList.cons_suffix_cons {α : Type} [MyEq α] (x : α) (xs ys : MyList α) : (MyList.my_cons x xs).is_suffix_of (MyList.my_cons x ys) = (MyEq.my_eq x x).my_and (xs.is_suffix_of ys) := by
  rw [MyList.is_suffix_of, MyEq.my_eq_refl x]

theorem MyList.prefix_inverse_suffix {α : Type} [MyEq α] (xs ys : MyList α) : xs.is_prefix_of ys = (MyList.my_reverse xs).is_suffix_of (MyList.my_reverse ys) := by
  rfl

theorem MyList.suffix_append {α : Type} [MyEq α] (xs ys : MyList α) : xs.is_suffix_of (xs.my_append ys) = MyBool.my_true := by
  induction xs with
  | my_nil => rfl
  | my_cons x _ ih =>
    rw [MyList.cons_append, MyList.cons_suffix_cons, MyEq.my_eq_refl x, ih, MyBool.true_and_true]

theorem MyList.prefix_prepend {α : Type} [MyEq α] (xs ys : MyList α) : xs.is_prefix_of (ys.my_append xs) = MyBool.my_true := by
  rw [MyList.prefix_inverse_suffix, MyList.append_reverse, MyList.suffix_append]

/- Replicate Theorems -/
theorem MyList.zero_rep_is_nil {α : Type} (x : α) : MyList.replicate MyNat.my_zero x = MyList.my_nil := by
  rfl

theorem MyList.rep_succ_eq_cons_rep {α : Type} (n : MyNat) (x : α) : MyList.replicate n.my_succ x = MyList.my_cons x (MyList.replicate n x) := by
  rfl

theorem MyList.rep_length {α : Type} (n : MyNat) (x : α) : (MyList.replicate n x).my_length = n := by
  induction n with
  | my_zero => rfl
  | my_succ _ ih =>
    rw [MyList.rep_succ_eq_cons_rep, MyList.cons_length, ih]

end Leftpad.ListTheorems
