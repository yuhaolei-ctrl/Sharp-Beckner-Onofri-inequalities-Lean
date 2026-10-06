module

public import BecknerOnofri.SpinPressureCertificateCore

namespace BecknerOnofri.HighDim.Spin.PressureCertificate
set_option profiler true
set_option profiler.threshold 1

def xx : Ctx := mkCtx 16 17 48
def a1 : Iv := ⟨123456789012345678901234567890, 123456789012345678901234567899⟩
def a2 : Iv := ⟨-923456789012345678901234567890, 723456789012345678901234567899⟩
def L5 : List Iv := [a1, a2, a1, a2, a1]
theorem v1 : decide (0 < (Iv.pow a1 200).hi) = true := by decide +kernel
theorem v2 : decide (0 < (Iv.pow a1 200).hi + (Iv.pow a1 200).lo) = true := by decide +kernel
theorem v3 : decide (0 < (prange (pmul L5 L5) xx.pows).hi) = true := by decide +kernel
theorem v4 : decide (0 < (prange (pmul (pmul L5 L5) (pmul L5 L5)) xx.pows).hi) = true := by decide +kernel
def L5' : List Iv := List.replicate 5 a1
theorem v5 : decide (0 < (prange (pmul L5' L5') xx.pows).hi) = true := by decide +kernel

end BecknerOnofri.HighDim.Spin.PressureCertificate
