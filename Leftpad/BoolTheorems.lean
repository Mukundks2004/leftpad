import Leftpad.MksBool

namespace Leftpad.BoolTheorems

open Leftpad.MksBool

theorem MyBool.true_and_true : MyBool.my_true.my_and MyBool.my_true = MyBool.my_true := by
  rfl

end Leftpad.BoolTheorems
