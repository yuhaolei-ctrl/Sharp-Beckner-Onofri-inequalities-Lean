module

public import BecknerOnofri.RawAttainment
public import BecknerOnofri.BesselIntegral
public import Legacy.BecknerOnofri.SubcriticalFourierVariation
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Sharpness of the physical spectral coefficient from actual first-shell potentials. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace BecknerOnofri.HighDim
open Legacy.BecknerOnofri.TorusSobolev
open Legacy.BecknerOnofri.SubcriticalAttainment
open Legacy.BecknerOnofri.SubcriticalEuler

lemma axisFrequency_ne_zero {d : ℕ} (j : Fin d) : axisFrequency j ≠ 0 := by
  intro h
  have := congrFun h j
  simp [axisFrequency] at this

lemma axisFrequency_eq_single {d : ℕ} (j : Fin d) :
    axisFrequency j = Pi.single j 1 := by
  classical
  ext i
  by_cases h : i = j <;> simp [axisFrequency, h]

lemma mFourier_axisFrequency {d : ℕ} (j : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency j) x = fourier 1 (x j) := by
  classical
  rw [axisFrequency_eq_single]
  exact UnitAddTorus.mFourier_single x j

lemma frequencyRadius_axisFrequency {d : ℕ} (j : Fin d) :
    Legacy.TorusEndpoint.frequencyRadius (axisFrequency j) = 1 := by
  classical
  simp [Legacy.TorusEndpoint.frequencyRadius, axisFrequency]

/-- The L² Fourier mode with coefficients t at ±e_j. -/
def firstShellLp {d : ℕ} (j : Fin d) (t : ℝ) : TorusL2 d :=
  mode (axisFrequency j) (t : ℂ)

lemma firstShellLp_admissible {d : ℕ} (j : Fin d) (t : ℝ) :
    Admissible (firstShellLp j t) :=
  ⟨mode_real _ _, mode_criticalSobolev (axisFrequency_ne_zero j) _⟩

lemma firstShellLp_coe {d : ℕ} (j : Fin d) (t : ℝ) :
    (fun x => ((firstShellLp j t) x).re) =ᵐ[torusMeasure d]
      (fun x => 2 * t * circleCosine (x j)) := by
  filter_upwards [mode_coe (axisFrequency j) (t : ℂ)] with x hx
  change ((mode (axisFrequency j) (t : ℂ)) x).re = _
  rw [hx, UnitAddTorus.mFourier_neg, mFourier_axisFrequency]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero]
  unfold circleCosine
  ring

lemma firstShellLp_energy {d : ℕ} (j : Fin d) (t : ℝ) :
    criticalEnergy (firstShellLp j t) = 2 * t ^ 2 := by
  have h := energy_perturb (admissible_zero d) (axisFrequency_ne_zero j) (t : ℂ) 1
  simpa [perturb, firstShellLp, frequencyRadius_axisFrequency, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

lemma firstShellLp_partition {d : ℕ} (j : Fin d) (t : ℝ) :
    partition (firstShellLp j t) = besselI0Two t := by
  unfold partition
  calc
    _ = ∫ x : Torus d, Real.exp (2 * t * circleCosine (x j)) ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [firstShellLp_coe j t] with x hx
      rw [hx]
    _ = ∫ x : UnitAddCircle, Real.exp (2 * t * circleCosine x) ∂AddCircle.haarAddCircle := by
      exact integral_comp_eval (μ := fun _ : Fin d => AddCircle.haarAddCircle)
        (i := j) (f := fun x => Real.exp (2 * t * circleCosine x))
        (by unfold circleCosine; fun_prop)
    _ = besselI0Two t := (besselI0Two_eq_circle_integral t).symm

lemma one_add_sq_le_besselI0Two (t : ℝ) : 1 + t ^ 2 ≤ besselI0Two t := by
  have h := (besselI0Two_summable t).sum_le_tsum (s := Finset.range 2)
    (fun n _ => div_nonneg (by simpa [pow_mul] using pow_nonneg (sq_nonneg t) n)
      (by positivity))
  simpa [besselI0Two, Finset.sum_range_succ] using h

lemma log_besselI0Two_lower (t : ℝ) :
    t ^ 2 - t ^ 4 / 2 ≤ Real.log (besselI0Two t) := by
  have hs := sq_nonneg t
  have hlog := Real.le_log_one_add_of_nonneg hs
  have hden : 0 < t ^ 2 + 2 := by positivity
  have hpoly : t ^ 2 - t ^ 4 / 2 ≤ 2 * t ^ 2 / (t ^ 2 + 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg (t ^ 3)]
  exact hpoly.trans (hlog.trans (Real.log_le_log (by positivity)
    (one_add_sq_le_besselI0Two t)))

/-- Every coefficient strictly below the spectral value has strictly positive defect.
The witness is the actual mode 2√(1−2A(2π)^d) cos(2πx₁). -/
theorem coefficientDefect_pos_of_lt_spectral {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : A < spectralCoefficient d) : 0 < coefficientDefect d A := by
  let j : Fin d := ⟨0, hd⟩
  let δ : ℝ := 1 - 2 * A * (2 * Real.pi) ^ d
  have hc : 0 < 2 * (2 * Real.pi) ^ d := by positivity
  have hδ : 0 < δ := by
    have hh := (lt_div_iff₀ hc).mp hA
    dsimp [δ]
    nlinarith
  let t : ℝ := Real.sqrt δ
  have ht : t ^ 2 = δ := Real.sq_sqrt hδ.le
  let u := firstShellLp j t
  have hu : Admissible u := firstShellLp_admissible j t
  have hpos : 0 < functional (A * (2 * Real.pi) ^ d) u := by
    change 0 < Real.log (partition (firstShellLp j t)) -
      (A * (2 * Real.pi) ^ d) * criticalEnergy (firstShellLp j t)
    rw [firstShellLp_partition, firstShellLp_energy]
    have hlower := log_besselI0Two_lower t
    have hfour : t ^ 4 = δ ^ 2 := by nlinarith [sq_nonneg (t ^ 2 - δ)]
    rw [ht, hfour] at hlower
    rw [ht]
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    dsimp [δ] at hlower hδsq ⊢
    nlinarith
  have hraw : (0 : EReal) < RawAttainment.rawFunctional A (RawAttainment.realValue u) := by
    rw [RawAttainment.rawFunctional_realValue hd A u hu]
    exact_mod_cast hpos
  apply hraw.trans_le
  unfold coefficientDefect RawAttainment.rawFunctional
  exact le_iSup_of_le (RawAttainment.realValue u)
    (le_iSup_of_le (RawAttainment.realValue_sobolev u hu) le_rfl)

#print axioms coefficientDefect_pos_of_lt_spectral

end BecknerOnofri.HighDim
