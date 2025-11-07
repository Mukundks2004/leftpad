import Leftpad.BoolTheorems
import Leftpad.ListTheorems
import Leftpad.MksBool
import Leftpad.MksList
import Leftpad.MksNat
import Leftpad.NatTheorems

namespace Leftpad.Leftpad

open Leftpad.BoolTheorems
open Leftpad.ListTheorems
open Leftpad.MksList
open Leftpad.MksNat
open Leftpad.MksBool
open Leftpad.NatTheorems

def Leftpad.leftpad {α : Type} (n : MyNat) (x : α) (xs : MyList α) : MyList α :=
  xs.my_append (MyList.replicate (n.my_sub xs.my_length) x)

theorem Leftpad.leftpad_rep_def {α : Type} (n : MyNat) (x : α) (xs : MyList α) : Leftpad.leftpad n x xs = xs.my_append (MyList.replicate (n.my_sub xs.my_length) x) := by
  rfl

theorem Leftpad.leftpad_length {α : Type} (n : MyNat) (x : α) (xs : MyList α) : (Leftpad.leftpad n x xs).my_length = n.my_max xs.my_length := by
  match n with
  | MyNat.my_zero =>
    rw [MyNat.zero_max, Leftpad.leftpad_rep_def, MyNat.zero_sub, MyList.zero_rep_is_nil, MyList.append_nil]
  | MyNat.my_succ n =>
    match xs with
    | MyList.my_nil => rw [Leftpad.leftpad_rep_def, MyList.nil_length, MyNat.sub_zero, MyList.nil_append, MyList.rep_length, MyNat.max_zero]
    | MyList.my_cons y ys =>
      rw [Leftpad.leftpad_rep_def, MyList.cons_length, MyNat.succ_sub_succ, MyList.append_length, MyList.cons_length, MyList.rep_length, MyNat.succ_max_succ, MyNat.succ_add, MyNat.add_sub_eq_max, MyNat.max_comm]

theorem Leftpad.leftpad_prefix {α : Type} [MyEq α] (n : MyNat) (x : α) (xs : MyList α) : (MyList.replicate (n.my_sub xs.my_length) x).is_prefix_of (Leftpad.leftpad n x xs) = MyBool.my_true := by
  rw [Leftpad.leftpad_rep_def, MyList.prefix_prepend]

theorem Leftpad.leftpad_suffix {α : Type} [MyEq α] (n : MyNat) (x : α) (xs : MyList α) : xs.is_suffix_of (Leftpad.leftpad n x xs) = MyBool.my_true := by
  rw [Leftpad.leftpad_rep_def, MyList.suffix_append]

end Leftpad.Leftpad

open Leftpad.Leftpad
open Leftpad.MksBool
open Leftpad.MksList
open Leftpad.MksNat

instance : MyEq Char where
  my_eq x y :=
    if x.val = y.val then MyBool.my_true else MyBool.my_false

  my_eq_refl (x : Char) : (if x.val = x.val then MyBool.my_true else MyBool.my_false) = MyBool.my_true := by
    simp

def toString {α : Type} (toStr : α → String) : MyList α → String
  | MyList.my_nil => ""
  | MyList.my_cons x xs => toString toStr xs ++ toStr x

def result := toString (fun c => String.mk [c]) (Leftpad.leftpad (MyNat.my_succ (MyNat.my_succ (MyNat.my_succ (MyNat.my_succ (MyNat.my_succ MyNat.my_zero))))) '!' (MyList.my_cons 'o' (MyList.my_cons 'o' (MyList.my_cons 'f' MyList.my_nil))))
