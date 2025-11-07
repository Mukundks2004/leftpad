import Leftpad.MksBool
import Leftpad.MksNat

namespace Leftpad.MksList

open Leftpad.MksBool
open Leftpad.MksNat

inductive MyList (α : Type) where
  | my_nil : MyList α
  | my_cons : α → MyList α → MyList α

def MyList.my_length {α : Type} : MyList α → MyNat
  | my_nil => MyNat.my_zero
  | my_cons _ xs => xs.my_length.my_succ

def MyList.my_append {α : Type} : MyList α → MyList α → MyList α
  | my_nil, ys => ys
  | my_cons x xs, ys => my_cons x (xs.my_append ys)

def MyList.my_reverse {α : Type} : MyList α → MyList α
  | my_nil => my_nil
  | my_cons x xs => xs.my_reverse.my_append (my_cons x my_nil)

def MyList.is_suffix_of {α : Type} [MyEq α] : MyList α → MyList α → MyBool
  | my_nil, _ => MyBool.my_true
  | my_cons a as, my_cons b bs => (MyEq.my_eq a b).my_and (as.is_suffix_of bs)
  | _, _ => MyBool.my_false

def MyList.is_prefix_of {α : Type} [MyEq α] : MyList α → MyList α → MyBool
  | as, bs => (as.my_reverse).is_suffix_of (bs.my_reverse)

def MyList.replicate {α : Type} : MyNat → α → MyList α
  | MyNat.my_zero, _ => my_nil
  | MyNat.my_succ n, x => my_cons x (MyList.replicate n x)

end Leftpad.MksList
