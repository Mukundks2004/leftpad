import Leftpad.MksBool

namespace Leftpad.BoolTheorems

open Leftpad.MksBool

theorem MyBool.and_true_left (b : MyBool) : MyBool.my_true.my_and b = b := by
  match b with
  | MyBool.my_true => rfl
  | MyBool.my_false => rfl

end Leftpad.BoolTheorems
