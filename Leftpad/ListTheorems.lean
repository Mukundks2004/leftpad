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

theorem MyList.nil_append {α : Type} (xs : MyList α) : MyList.my_nil.my_append xs = xs := by
  rfl

theorem MyList.append_nil {α : Type} (xs : MyList α) : xs.my_append MyList.my_nil = xs := by
  induction xs with
    | my_nil => rfl
    | my_cons _ _ ih =>
      rw [MyList.my_append, ih]

theorem MyList.nil_length {α : Type} : (MyList.my_nil : MyList α).my_length = MyNat.my_zero := by
  rfl

theorem MyList.cons_length {α : Type} (x : α) (xs : MyList α) : (MyList.my_cons x xs).my_length = MyNat.my_succ xs.my_length := by
  rfl

theorem MyList.append_length {α : Type} (xs ys : MyList α) : (xs.my_append ys).my_length = xs.my_length.my_add ys.my_length := by
  induction xs with
  | my_nil =>
    rw [MyList.nil_append, MyList.nil_length, MyNat.zero_add]
  | my_cons _ _ ih =>
    rw [MyList.cons_length, MyList.my_append, MyList.cons_length, ih, MyNat.succ_add]

theorem MyList.replicate_length {α : Type} (n : MyNat) (x : α) : (MyList.replicate n x).my_length = n := by
  induction n with
  | my_zero =>
    rw [MyList.replicate, MyList.my_length]
  | my_succ _ ih =>
    rw [MyList.replicate, MyList.my_length, ih]

theorem MyList.zero_replicate_is_nil {α : Type} (x : α) : MyList.replicate MyNat.my_zero x = MyList.my_nil := by
  rfl

theorem MyList.list_is_suffix_of_itself {α : Type} [MyEq α] (xs : MyList α) : xs.is_suffix_of xs = MyBool.my_true := by
  induction xs with
  | my_nil => rfl
  | my_cons hd tl ih =>
    rw [MyList.is_suffix_of, MyEq.my_eq_refl hd, ih, MyBool.and_true_left]

theorem MyList.nil_is_suffix_of_any {α : Type} [MyEq α] (xs : MyList α) : MyList.my_nil.is_suffix_of xs = MyBool.my_true := by
  rfl

theorem MyList.append_cons {α : Type} (x : α) (xs ys : MyList α) : (MyList.my_cons x xs).my_append ys = MyList.my_cons x (xs.my_append ys) := by
  rfl

theorem MyList.list_is_suffix_after_append {α : Type} [MyEq α] (xs ys : MyList α) : xs.is_suffix_of (xs.my_append ys) = MyBool.my_true := by
  induction xs with
  | my_nil =>
    rw [MyList.nil_append, MyList.nil_is_suffix_of_any]
  | my_cons hd tl ih =>
    rw [MyList.append_cons, MyList.is_suffix_of, MyEq.my_eq_refl hd, ih, MyBool.and_true_left]

theorem MyList.reverse_nil {α : Type} : MyList.my_reverse (MyList.my_nil : MyList α) = MyList.my_nil := by
  rfl

theorem MyList.nil_is_prefix_of_any {α : Type} [MyEq α] (xs : MyList α) : MyList.my_nil.is_prefix_of xs = MyBool.my_true := by
  rw [MyList.is_prefix_of, MyList.reverse_nil, MyList.nil_is_suffix_of_any]

theorem MyList.cons_reverse {α : Type} (x : α) (xs : MyList α) : MyList.my_reverse (MyList.my_cons x xs) = MyList.my_append (MyList.my_reverse xs) (MyList.my_cons x MyList.my_nil) := by
  rfl

theorem MyList.append_assoc {α : Type} (xs ys zs : MyList α) : xs.my_append (ys.my_append zs)  = (xs.my_append ys).my_append zs := by
  match xs with
  | MyList.my_nil => rfl
  | MyList.my_cons hd tl =>
    rw [MyList.my_append, MyList.my_append, MyList.my_append, MyList.append_assoc tl ys zs]

theorem MyList.append_reverse {α : Type} (xs ys : MyList α) : MyList.my_reverse (xs.my_append ys) = MyList.my_append (MyList.my_reverse ys) (MyList.my_reverse xs) := by
  induction xs with
  | my_nil =>
    rw [MyList.nil_append, MyList.reverse_nil, MyList.append_nil]
  | my_cons hd tl ih =>
    rw [MyList.append_cons, MyList.cons_reverse, MyList.cons_reverse, MyList.append_assoc, ih]

theorem MyList.reverse_is_suffix_after_append {α : Type} [MyEq α] (xs ys : MyList α) : (MyList.my_reverse xs).is_suffix_of (MyList.my_reverse (ys.my_append xs)) = MyBool.my_true := by
  rw [MyList.append_reverse, MyList.list_is_suffix_after_append]

theorem MyList.is_prefix_after_append {α : Type} [MyEq α] (xs ys : MyList α) : xs.is_prefix_of (ys.my_append xs) = MyBool.my_true := by
  rw [MyList.is_prefix_of, MyList.reverse_is_suffix_after_append]

end Leftpad.ListTheorems
