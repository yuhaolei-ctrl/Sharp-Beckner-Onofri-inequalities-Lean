import BecknerOnofri.EntropyHeatCheckedPanels

namespace BecknerOnofri.HighDim.EntropyTail.HeatCertificate

def panelScale : ℕ := 10^30

structure IntegerPanel where
  left : ℤ
  right : ℤ
  upper : ℤ
  deriving DecidableEq

def IntegerPanel.rationalPanel (p : IntegerPanel) : RationalPanel :=
  ⟨(p.left : ℚ)/panelScale, (p.right : ℚ)/panelScale, (p.upper : ℚ)/panelScale⟩

def IntegerPanel.weight (p : IntegerPanel) (z : ℤ) : ℤ :=
  p.upper*((max (p.right-z) 0)^6-(max (p.left-z) 0)^6)

theorem scaled_positive_part (a : ℤ) :
    max ((a : ℚ)/panelScale) 0 = ((max a 0 : ℤ) : ℚ)/panelScale := by
  simp only [Int.cast_max, Int.cast_zero]
  simpa only [zero_div] using (max_div_div_right
    (by norm_num [panelScale] : (0 : ℚ) ≤ panelScale) (a : ℚ) (0 : ℚ))

theorem IntegerPanel.weight_eq (p : IntegerPanel) (z : ℤ) :
    p.rationalPanel.weight ((z : ℚ)/panelScale) =
      (p.weight z : ℚ)/(720*(panelScale : ℚ)^7) := by
  dsimp only [RationalPanel.weight, IntegerPanel.rationalPanel]
  rw [← sub_div, ← sub_div, ← Int.cast_sub p.right z, ← Int.cast_sub p.left z,
    scaled_positive_part, scaled_positive_part]
  simp only [IntegerPanel.weight, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_max, Int.cast_zero]
  ring

def integerPanelWeight (ps : List IntegerPanel) (z : ℤ) : ℤ :=
  (ps.map (fun p => p.weight z)).sum

theorem integerPanelWeight_eq (ps : List IntegerPanel) (z : ℤ) :
    ((ps.map IntegerPanel.rationalPanel).map (fun p => p.weight ((z : ℚ)/panelScale))).sum =
      (integerPanelWeight ps z : ℚ)/(720*(panelScale : ℚ)^7) := by
  induction ps with
  | nil => simp [integerPanelWeight]
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, IntegerPanel.weight_eq]
    rw [ih]
    simp only [integerPanelWeight, List.map_cons, List.sum_cons, Int.cast_add]
    ring

theorem PanelBlock.weight_eq_integer (b : PanelBlock) (ps : List IntegerPanel)
    (h : b.panels.map EndpointPanel.rationalPanel = ps.map IntegerPanel.rationalPanel) (z : ℤ) :
    b.weight ((z : ℚ)/panelScale) =
      (integerPanelWeight ps z : ℚ)/(720*(panelScale : ℚ)^7) := by
  calc
    _ = ((b.panels.map EndpointPanel.rationalPanel).map
        (fun p => p.weight ((z : ℚ)/panelScale))).sum := by
      simp only [PanelBlock.weight, List.map_map, Function.comp_def]
    _ = _ := by rw [h, integerPanelWeight_eq]

#print axioms PanelBlock.weight_eq_integer
end BecknerOnofri.HighDim.EntropyTail.HeatCertificate
