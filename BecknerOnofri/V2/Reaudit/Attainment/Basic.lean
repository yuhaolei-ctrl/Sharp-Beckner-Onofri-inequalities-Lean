module

public import BecknerOnofri.RawAttainment
public import BecknerOnofri.PartitionRegularity
public import BecknerOnofri.Uniform
public import BecknerOnofri.FullHessianDecomposition

@[expose] public section

/-! # Elementary facts about raw critical Sobolev potentials (package `Attainment`)

Centering and multiplication by a real constant preserve `InCriticalSobolev`; they change the
seminorm `potentialEnergy` in the expected way.  These are used to apply the critical Adams bound
to `2 u_n` and to pass from `u` to `u - ū` in the direct method (S010). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

theorem potentialEnergy_nonneg (u : Torus d → ℝ) : 0 ≤ potentialEnergy u :=
  tsum_nonneg fun k => by unfold potentialTerm frequencyLength; positivity

theorem fourierCoeff_const_mul (c : ℝ) (u : Torus d → ℝ) (k : Frequency d) :
    fourierCoeff (fun x => c * u x) k = (c : ℂ) * fourierCoeff u k := by
  unfold BecknerOnofri.HighDim.fourierCoeff
  have : ∀ x : Torus d, UnitAddTorus.mFourier (-k) x * (((c * u x : ℝ)) : ℂ) =
      (c : ℂ) * (UnitAddTorus.mFourier (-k) x * (u x : ℂ)) := fun x => by push_cast; ring
  simp_rw [this]
  rw [integral_const_mul]

theorem fourierCoeff_const_nonzero (c : ℝ) {k : Frequency d} (hk : k ≠ 0) :
    fourierCoeff (fun _ : Torus d => c) k = 0 := by
  have h := fourierCoeff_const_mul c (fun _ : Torus d => (1 : ℝ)) k
  simp only [mul_one] at h
  rw [h, fourierCoeff_one_nonzero k hk, mul_zero]

theorem fourierCoeff_centered {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d))
    {k : Frequency d} (hk : k ≠ 0) : fourierCoeff (centered u) k = fourierCoeff u k := by
  have h := FullHessianDecomposition.fourierCoeff_sub u (fun _ => ∫ y, u y ∂torusMeasure d) hu
    (memLp_const _) k
  rw [fourierCoeff_const_nonzero _ hk, sub_zero] at h
  exact h

theorem potentialEnergy_centered {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d)) :
    potentialEnergy (centered u) = potentialEnergy u := by
  unfold potentialEnergy
  refine tsum_congr fun k => ?_
  simp only [potentialTerm, fourierCoeff_centered hu k.2]

theorem inCriticalSobolev_centered {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    InCriticalSobolev (centered u) := by
  refine ⟨hu.1.sub (memLp_const _), ?_⟩
  have : potentialTerm (centered u) = potentialTerm u := by
    funext k
    simp only [potentialTerm, fourierCoeff_centered hu.1 k.2]
  rw [this]
  exact hu.2

theorem meanZero_centered {u : Torus d → ℝ} (hu : MemLp u 2 (torusMeasure d)) :
    MeanZero (centered u) :=
  centered_integral u (hu.integrable (by norm_num))

theorem centered_eq_self {u : Torus d → ℝ} (hm : MeanZero u) : centered u = u := by
  funext x
  have : (∫ y, u y ∂torusMeasure d) = 0 := hm
  simp [centered, this]

theorem inCriticalSobolev_const_mul (c : ℝ) {u : Torus d → ℝ} (hu : InCriticalSobolev u) :
    InCriticalSobolev (fun x => c * u x) := by
  refine ⟨hu.1.const_mul c, ?_⟩
  refine (hu.2.mul_left (c ^ 2)).congr fun k => ?_
  simp only [potentialTerm, fourierCoeff_const_mul, norm_mul, Complex.norm_real, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

theorem potentialEnergy_const_mul (c : ℝ) (u : Torus d → ℝ) :
    potentialEnergy (fun x => c * u x) = c ^ 2 * potentialEnergy u := by
  unfold potentialEnergy
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [potentialTerm, fourierCoeff_const_mul, norm_mul, Complex.norm_real, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

theorem meanZero_const_mul (c : ℝ) {u : Torus d → ℝ} (hm : MeanZero u) :
    MeanZero (fun x => c * u x) := by
  have : (∫ y, u y ∂torusMeasure d) = 0 := hm
  unfold MeanZero
  rw [integral_const_mul, this, mul_zero]

end BecknerOnofri.V2.Reaudit.Attainment
