namespace Leftpad.MksNat

inductive MyNat where
  | my_zero : MyNat
  | my_succ : MyNat → MyNat

def MyNat.my_add : MyNat → MyNat → MyNat
  | m, my_zero => m
  | m, my_succ n => my_succ (my_add m n)

def MyNat.my_sub : MyNat → MyNat → MyNat
  | m, my_zero => m
  | my_zero, _ => my_zero
  | my_succ m, my_succ n => my_sub m n

def MyNat.my_max : MyNat → MyNat → MyNat
  | my_zero, n => n
  | m, my_zero => m
  | my_succ m, my_succ n => my_succ (my_max m n)

end Leftpad.MksNat
