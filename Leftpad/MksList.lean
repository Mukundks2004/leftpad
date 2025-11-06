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
  | my_cons _ xs => MyNat.my_succ (MyList.my_length xs)

def MyList.my_append {α : Type} : MyList α → MyList α → MyList α
  | my_nil, ys => ys
  | my_cons x xs, ys => my_cons x (MyList.my_append xs ys)

def MyList.my_reverse {α : Type} : MyList α → MyList α
  | my_nil => my_nil
  | my_cons x xs => MyList.my_append (MyList.my_reverse xs) (my_cons x my_nil)

def MyList.is_suffix_of {α : Type} [MyEq α] : MyList α → MyList α → MyBool
  | my_nil, _ => MyBool.my_true
  | my_cons a as, my_cons b bs => MyBool.my_and (MyEq.my_eq a b) (is_suffix_of as bs)
  | _, _ => MyBool.my_false

def MyList.is_prefix_of {α : Type} [MyEq α] : MyList α → MyList α → MyBool
  | as, bs => MyList.is_suffix_of (MyList.my_reverse as) (MyList.my_reverse bs)

def MyList.replicate {α : Type} : MyNat → α → MyList α
  | MyNat.my_zero, _ => my_nil
  | MyNat.my_succ n, x => my_cons x (MyList.replicate n x)

end Leftpad.MksList
