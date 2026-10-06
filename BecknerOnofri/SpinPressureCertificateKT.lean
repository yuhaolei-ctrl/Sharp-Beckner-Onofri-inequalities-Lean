module

public import BecknerOnofri.SpinPressureCertificateCore

namespace BecknerOnofri.HighDim.Spin.PressureCertificate
def xl : Ctx := ⟨⟨435754893828453856764491726848, 435754893828453856764491726848⟩, [⟨1267650600228229401496703205376, 1267650600228229401496703205376⟩, ⟨-13204693752377389598923991723, 13204693752377389598923991723⟩, ⟨0, 137548893253931141655458248⟩, ⟨-1432800971395116058911024, 1432800971395116058911024⟩, ⟨0, 14925010118699125613657⟩, ⟨-155468855403115891809, 155468855403115891809⟩, ⟨0, 1619467243782457207⟩, ⟨-16869450456067263, 16869450456067263⟩, ⟨0, 175723442250701⟩, ⟨-1830452523445, 1830452523445⟩, ⟨0, 19067213786⟩]⟩
def xx : Ctx := mkCtx 16 17 48
def chk (y : Ctx) (X : TM) : Bool := X.ok && decide (0 < (TM.range y X).hi + 1)
def zpow (y : Ctx) : Nat → TM
  | 0 => TM.sub (TM.var y) (TM.scal (Iv.ofRat 1 4) (TM.mul y (TM.var y) (TM.mul y (TM.var y) (TM.var y))))
  | n + 1 => TM.mul y (zpow y n) (zpow y 0)
set_option profiler true
set_option profiler.threshold 0
theorem kt_target : (chk xl (zpow xl 24)) = true := by decide +kernel
end BecknerOnofri.HighDim.Spin.PressureCertificate
