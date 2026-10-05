import BecknerOnofri.Definitions
import BecknerOnofri.BesselIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual first-shell Gibbs densities and their product Haar integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim

def firstShellPotential {d : ℕ} (t : Fin d → ℝ) (x : Torus d) : ℝ :=
  ∑ i : Fin d, 2 * t i * circleCosine (x i)

def circleTiltDensity (t : ℝ) (x : UnitAddCircle) : ℝ :=
  Real.exp (2 * t * circleCosine x) / besselI0Two t

def firstShellTilt {d : ℕ} (t : Fin d → ℝ) (x : Torus d) : ℝ :=
  ∏ i : Fin d, circleTiltDensity (t i) (x i)

lemma besselI0Two_pos (t : ℝ) : 0 < besselI0Two t :=
  zero_lt_one.trans_le (one_le_besselI0Two t)

lemma firstShell_partition {d : ℕ} (t : Fin d → ℝ) :
    (∫ x, Real.exp (firstShellPotential t x) ∂torusMeasure d) =
      ∏ i : Fin d, besselI0Two (t i) := by
  unfold firstShellPotential torusMeasure
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i : Fin d => fun x : UnitAddCircle =>
    Real.exp (2 * t i * circleCosine x))]
  simp_rw [← besselI0Two_eq_circle_integral]

lemma firstShell_log_partition_quartic {d : ℕ} (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i) (ht' : ∀ i, t i ≤ 1 / 5) :
    Real.log (∫ x, Real.exp (firstShellPotential t x) ∂torusMeasure d) ≤
      (∑ i, t i ^ 2) - (6 / 25 : ℝ) * ∑ i, t i ^ 4 := by
  rw [firstShell_partition, Real.log_prod (fun i _ => (besselI0Two_pos (t i)).ne')]
  calc
    _ ≤ ∑ i : Fin d, (t i ^ 2 - (6 / 25 : ℝ) * t i ^ 4) :=
      Finset.sum_le_sum (fun i _ => log_besselI0Two_quartic (ht i) (ht' i))
    _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]

lemma circleTiltDensity_pos (t : ℝ) (x : UnitAddCircle) : 0 < circleTiltDensity t x :=
  div_pos (Real.exp_pos _) (besselI0Two_pos t)

lemma circleTiltDensity_integral (t : ℝ) :
    (∫ x : UnitAddCircle, circleTiltDensity t x ∂AddCircle.haarAddCircle) = 1 := by
  unfold circleTiltDensity
  rw [integral_div, ← besselI0Two_eq_circle_integral, div_self (besselI0Two_pos t).ne']

lemma firstShellTilt_pos {d : ℕ} (t : Fin d → ℝ) (x : Torus d) :
    0 < firstShellTilt t x := Finset.prod_pos (fun _ _ => circleTiltDensity_pos _ _)

lemma firstShellTilt_integral {d : ℕ} (t : Fin d → ℝ) :
    (∫ x, firstShellTilt t x ∂torusMeasure d) = 1 := by
  unfold firstShellTilt torusMeasure
  rw [integral_fintype_prod_eq_prod]
  simp_rw [circleTiltDensity_integral]
  simp

lemma firstShellTilt_eq_exp {d : ℕ} (t : Fin d → ℝ) (x : Torus d) :
    firstShellTilt t x = Real.exp (firstShellPotential t x) /
      (∫ y, Real.exp (firstShellPotential t y) ∂torusMeasure d) := by
  rw [firstShell_partition]
  unfold firstShellTilt circleTiltDensity firstShellPotential
  rw [Finset.prod_div_distrib, Real.exp_sum]

lemma firstShellTilt_integrable {d : ℕ} (t : Fin d → ℝ) :
    Integrable (firstShellTilt t) (torusMeasure d) := by
  apply Continuous.integrable_of_hasCompactSupport
  · unfold firstShellTilt circleTiltDensity circleCosine
    fun_prop
  · exact HasCompactSupport.of_compactSpace _

/-- The actual normalized first-shell Gibbs density. -/
def firstShellDensity {d : ℕ} (t : Fin d → ℝ) : ProbabilityDensity d where
  value := firstShellTilt t
  nonneg := Filter.Eventually.of_forall (fun x => (firstShellTilt_pos t x).le)
  integrable := firstShellTilt_integrable t
  mass := firstShellTilt_integral t

def circleTiltFourier (t : ℝ) (k : ℤ) : ℂ :=
  ∫ x : UnitAddCircle, fourier (-k) x * (circleTiltDensity t x : ℂ)
    ∂AddCircle.haarAddCircle

lemma firstShellTilt_fourier {d : ℕ} (t : Fin d → ℝ) (k : Frequency d) :
    fourierCoeff (firstShellTilt t) k = ∏ i : Fin d, circleTiltFourier (t i) (k i) := by
  unfold fourierCoeff firstShellTilt torusMeasure UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Pi.neg_apply, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_eq_prod (fun i : Fin d => fun x : UnitAddCircle =>
    fourier (-k i) x * (circleTiltDensity (t i) x : ℂ))
    (μ := fun _ : Fin d => AddCircle.haarAddCircle)

#print axioms firstShell_log_partition_quartic
#print axioms firstShellTilt_fourier
end BecknerOnofri.HighDim
