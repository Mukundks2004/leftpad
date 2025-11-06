namespace Leftpad.MksBool

inductive MyBool where
  | my_true : MyBool
  | my_false : MyBool

class MyEq (α : Type) where
  my_eq : α → α → MyBool
  my_eq_refl : (x : α) → my_eq x x = MyBool.my_true

instance : MyEq MyBool where
  my_eq
    | .my_true, .my_true => .my_true
    | .my_false, .my_false => .my_true
    | _, _ => .my_false

  my_eq_refl x := by
    match x with
    | .my_true => rfl
    | .my_false => rfl

def MyBool.my_and : MyBool → MyBool → MyBool
  | .my_true, .my_true => .my_true
  | _, _ => .my_false

end Leftpad.MksBool
