import Legacy.BecknerOnofri.EulerCosineProfile
import Legacy.BecknerOnofri.FiniteDifferenceSmooth
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Steiner monotonicity becomes genuine coordinate monotonicity of the
closed cosine profile, including its boundary. Its first derivatives are
the actual Fréchet derivatives within the closed cube. -/
noncomputable section
namespace Legacy.BecknerOnofri.CubeProfileMonotone
open Set Legacy.TorusEndpoint ChebyshevProfile SteinerSelection SteinerFromPolarization
open scoped ContDiff

def angle (s : ℝ) : ℝ := Real.arccos s / (2 * Real.pi)

def inverseCos {d : ℕ} (z : Fin d → ℝ) : Fin d → ℝ := fun i => angle (z i)

theorem angle_mem (s : ℝ) : angle s ∈ Icc (0 : ℝ) (1/2) := by
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · exact div_nonneg (Real.arccos_nonneg s) hp.le
  · rw [angle, div_le_iff₀ hp]
    nlinarith [Real.arccos_le_pi s]

theorem angle_antitone : Antitone angle := by
  intro s t hst
  exact div_le_div_of_nonneg_right (Real.arccos_le_arccos hst) (by positivity)

theorem cos_angle {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    Real.cos (2 * Real.pi * angle s) = s := by
  rw [angle, mul_div_cancel₀ _ (by positivity : 2 * Real.pi ≠ 0)]
  exact Real.cos_arccos hs.1 hs.2

theorem cosinePoint_inverseCos {d : ℕ} {z : Fin d → ℝ}
    (hz : z ∈ ChebyshevProfile.closedCube d) : cosinePoint (inverseCos z) = z := by
  funext i
  exact cos_angle (mem_closedCube.mp hz i)

theorem quotient_update {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    SmoothFourier.quotient (Function.update x i s) = slice (SmoothFourier.quotient x) i s := by
  funext j
  by_cases h : j = i
  · subst j; simp [SmoothFourier.quotient, slice]
  · simp [SmoothFourier.quotient, slice, Function.update_of_ne h]

theorem cosinePoint_update_inverseCos {d : ℕ} {z : Fin d → ℝ}
    (hz : z ∈ ChebyshevProfile.closedCube d) (i : Fin d) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    cosinePoint (Function.update (inverseCos z) i (angle s)) = Function.update z i s := by
  funext j
  by_cases h : j = i
  · subst j
    simpa [cosinePoint] using cos_angle hs
  · simpa [cosinePoint, inverseCos, Function.update_of_ne h] using
      cos_angle (mem_closedCube.mp hz j)

theorem coordinate_monotone_of_steiner {d : ℕ} {f : Torus d → ℝ}
    {g : (Fin d → ℝ) → ℝ} (hSteiner : Steiner f)
    (hfactor : ∀ x : Fin d → ℝ, f (SmoothFourier.quotient x) = g (cosinePoint x))
    {z : Fin d → ℝ} (hz : z ∈ ChebyshevProfile.closedCube d) (i : Fin d) :
    MonotoneOn (fun s => g (Function.update z i s)) (Icc (-1 : ℝ) 1) := by
  intro s hs t ht hst
  have h := hSteiner.2 (SmoothFourier.quotient (inverseCos z)) i
    (angle_mem t) (angle_mem s) (angle_antitone hst)
  dsimp only at h ⊢
  rw [← quotient_update, ← quotient_update, hfactor, hfactor,
    cosinePoint_update_inverseCos hz i hs, cosinePoint_update_inverseCos hz i ht] at h
  exact h

def fromUnitCube {d : ℕ} (y : Fin d → ℝ) : Fin d → ℝ := fun i => 2*y i-1

theorem fromUnitCube_mapsTo (d : ℕ) :
    MapsTo (@fromUnitCube d) (FiniteDifferences.closedCube d) (ChebyshevProfile.closedCube d) := by
  intro y hy
  apply mem_closedCube.mpr
  intro i
  have h0 := hy.1 i
  have h1 := hy.2 i
  change 0 ≤ y i at h0
  change y i ≤ 1 at h1
  change -1 ≤ 2*y i-1 ∧ 2*y i-1 ≤ 1
  constructor <;> linarith

theorem fromUnitCube_update {d : ℕ} (y : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    fromUnitCube (Function.update y i s) = Function.update (fromUnitCube y) i (2*s-1) := by
  funext j
  by_cases h : j = i
  · subst j; simp [fromUnitCube]
  · simp [fromUnitCube, Function.update_of_ne h]

theorem fromUnitCube_contDiff (d : ℕ) : ContDiff ℝ ∞ (@fromUnitCube d) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_const.mul (contDiff_apply ℝ ℝ i)).sub contDiff_const

theorem unit_profile_contDiffOn {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hg : ContDiffOn ℝ ∞ g (ChebyshevProfile.closedCube d)) :
    ContDiffOn ℝ ∞ (fun y => g (fromUnitCube y)) (FiniteDifferences.closedCube d) :=
  hg.comp (fromUnitCube_contDiff d).contDiffOn (fromUnitCube_mapsTo d)

theorem unit_coordinate_monotone_of_steiner {d : ℕ} {f : Torus d → ℝ}
    {g : (Fin d → ℝ) → ℝ} (hSteiner : Steiner f)
    (hfactor : ∀ x : Fin d → ℝ, f (SmoothFourier.quotient x) = g (cosinePoint x))
    {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d) (i : Fin d) :
    MonotoneOn (fun s => g (fromUnitCube (Function.update y i s))) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  dsimp only
  rw [fromUnitCube_update, fromUnitCube_update]
  apply coordinate_monotone_of_steiner hSteiner hfactor (fromUnitCube_mapsTo d hy) i
  · constructor <;> linarith [hs.1, hs.2]
  · constructor <;> linarith [ht.1, ht.2]
  · linarith

theorem coordinateDerivative_nonneg {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (FiniteDifferences.closedCube d)) (i : Fin d)
    {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d)
    (hm : MonotoneOn (fun s => f (Function.update y i s)) (Icc (0 : ℝ) 1)) :
    0 ≤ FiniteDifferences.coordinateDerivative i f y := by
  have hd := FiniteDifferences.hasDerivWithinAt_coordinate_of_contDiffOn hf i hy
  have huniq := uniqueDiffOn_Icc_zero_one (y i) ⟨hy.1 i, hy.2 i⟩
  rw [← hd.derivWithin huniq]
  exact hm.derivWithin_nonneg

theorem first_derivative_nonneg_of_steiner {d : ℕ} {f : Torus d → ℝ}
    {g : (Fin d → ℝ) → ℝ} (hg : ContDiffOn ℝ ∞ g (ChebyshevProfile.closedCube d))
    (hSteiner : Steiner f)
    (hfactor : ∀ x : Fin d → ℝ, f (SmoothFourier.quotient x) = g (cosinePoint x))
    (i : Fin d) {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d) :
    0 ≤ FiniteDifferences.coordinateDerivative i (fun y => g (fromUnitCube y)) y :=
  coordinateDerivative_nonneg (unit_profile_contDiffOn hg) i hy
    (unit_coordinate_monotone_of_steiner hSteiner hfactor hy i)

theorem profile_gibbs_identity {d : ℕ} (u : TorusSobolev.TorusL2 d)
    {g h : (Fin d → ℝ) → ℝ}
    (hg : ∀ x : Fin d → ℝ, (WienerFourier.representative u (SmoothFourier.quotient x)).re =
      g (cosinePoint x))
    (hh : ∀ x : Fin d → ℝ, SmoothFourier.smoothGibbsValue u (SmoothFourier.quotient x) =
      h (cosinePoint x))
    {z : Fin d → ℝ} (hz : z ∈ ChebyshevProfile.closedCube d) :
    h z = Real.exp (g z) / SubcriticalAttainment.partition u := by
  have hg' := hg (inverseCos z)
  have hh' := hh (inverseCos z)
  rw [cosinePoint_inverseCos hz] at hg' hh'
  rw [← hh', SmoothFourier.smoothGibbsValue, hg']

#print axioms first_derivative_nonneg_of_steiner
#print axioms profile_gibbs_identity
end Legacy.BecknerOnofri.CubeProfileMonotone
