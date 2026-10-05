import BecknerOnofri.ContinuousGibbs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Actual first and second derivatives of entropy along a continuous
perturbation of the uniform density. Uniform positivity justifies both
passes of differentiation under the Haar integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.HighDim.UniformEntropy
open ContinuousGibbs

lemma perturbation_bounds {d : ℕ} (h : Space d) {t : ℝ}
    (ht : |t| < 1/(2*(‖h‖+1))) (x : Torus d) :
    (1/2:ℝ) < 1+t*h x ∧ 1+t*h x < 3/2 := by
  have hn := h.norm_coe_le_norm x
  have hab : |t*h x| < 1/2 := by
    rw [abs_mul]
    have hp : 0 < ‖h‖+1 := by positivity
    have ht' : |t| *(2*(‖h‖+1)) < 1 := (lt_div_iff₀ (by positivity)).mp ht
    rw [Real.norm_eq_abs] at hn
    nlinarith [abs_nonneg t, mul_le_mul_of_nonneg_left hn (abs_nonneg t)]
  constructor <;> linarith [(abs_lt.mp hab).1, (abs_lt.mp hab).2]

lemma entropy_hasDerivAt {d : ℕ} (h : Space d) {t : ℝ}
    (ht : |t| < 1/(2*(‖h‖+1))) :
    HasDerivAt (fun s : ℝ => ∫ x, (1+s*h x)*Real.log (1+s*h x) ∂torusMeasure d)
      (∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure d) t := by
  let J := {s : ℝ | |s| < 1/(2*(‖h‖+1))}
  have hJ : IsOpen J := isOpen_lt continuous_abs continuous_const
  have hp (s : ℝ) (hs : s ∈ J) (x : Torus d) : 0 < 1+s*h x :=
    lt_trans (by norm_num) (perturbation_bounds h hs x).1
  have hc (s : ℝ) : Continuous (fun x => 1+s*h x) := by fun_prop
  have hlog (s : ℝ) (hs : s ∈ J) := (hc s).log (fun x => (hp s hs x).ne')
  have hF (s : ℝ) (hs : s ∈ J) := (hc s).mul (hlog s hs)
  have hD (s : ℝ) (hs : s ∈ J) : Continuous (fun x => (Real.log (1+s*h x)+1)*h x) :=
    ((hlog s hs).add continuous_const).mul h.continuous
  have hb (s : ℝ) (hs : s ∈ J) (x : Torus d) :
      ‖(Real.log (1+s*h x)+1)*h x‖ ≤
        (|Real.log (1/2)|+|Real.log (3/2)|+1)*‖h‖ := by
    have hbounds := perturbation_bounds h hs x
    have hlo := Real.log_le_log (by norm_num : (0:ℝ)<1/2) hbounds.1.le
    have hhi := Real.log_le_log (hp s hs x) hbounds.2.le
    have hl : |Real.log (1+s*h x)| ≤ |Real.log (1/2)|+|Real.log (3/2)| :=
      abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (1/2)), abs_nonneg (Real.log (3/2))],
        by linarith [le_abs_self (Real.log (3/2)), abs_nonneg (Real.log (1/2))]⟩
    rw [norm_mul]
    apply mul_le_mul _ (h.norm_coe_le_norm x) (norm_nonneg _) (by positivity)
    simpa only [Real.norm_eq_abs, abs_one] using (abs_add_le (Real.log (1+s*h x)) 1).trans (by linarith)
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := torusMeasure d) (s := J)
    (F := fun s x => (1+s*h x)*Real.log (1+s*h x))
    (F' := fun s x => (Real.log (1+s*h x)+1)*h x)
    (bound := fun _ => (|Real.log (1/2)|+|Real.log (3/2)|+1)*‖h‖)
    (hJ.mem_nhds ht)
    (by filter_upwards [hJ.mem_nhds ht] with s hs; exact (hF s hs).aestronglyMeasurable)
    ((hF t ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hD t ht).aestronglyMeasurable
    (ae_of_all _ (fun x s hs => hb s hs x)) (integrable_const _)
    (ae_of_all _ (fun x s hs => by
      convert! (Real.hasDerivAt_mul_log (hp s hs x).ne').comp s
        (((hasDerivAt_id s).mul_const (h x)).const_add 1) using 1 <;> simp_all only [id_eq, one_mul, pow_one] <;> ring))
  exact H.2

lemma entropy_second_hasDerivAt {d : ℕ} (h : Space d) :
    HasDerivAt
      (fun t : ℝ => ∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure d)
      (∫ x, (h x)^2 ∂torusMeasure d) 0 := by
  let J := {s : ℝ | |s| < 1/(2*(‖h‖+1))}
  have hJ : J ∈ 𝓝 (0:ℝ) := (isOpen_lt continuous_abs continuous_const).mem_nhds (by
    change |(0:ℝ)| < _; simp only [abs_zero]; positivity)
  have hp (s : ℝ) (hs : s ∈ J) (x : Torus d) : 0 < 1+s*h x :=
    lt_trans (by norm_num) (perturbation_bounds h hs x).1
  have hc (s : ℝ) (hs : s ∈ J) : Continuous (fun x => (Real.log (1+s*h x)+1)*h x) := by
    apply Continuous.mul _ h.continuous
    exact ((by fun_prop : Continuous (fun x => 1+s*h x)).log (fun x => (hp s hs x).ne')).add continuous_const
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := torusMeasure d) (s := J)
    (F := fun s x => (Real.log (1+s*h x)+1)*h x)
    (F' := fun s x => (h x)^2/(1+s*h x)) (bound := fun _ => 2*‖h‖^2)
    hJ
    (by filter_upwards [hJ] with s hs; exact (hc s hs).aestronglyMeasurable)
    (by simpa using integrable d h)
    (by simpa only [zero_mul, add_zero, div_one] using
      (show AEStronglyMeasurable (fun x => (h x)^2) (torusMeasure d) from (h.continuous.pow 2).aestronglyMeasurable))
    (ae_of_all _ (fun x s hs => by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hp s hs x).le)]
      apply (div_le_iff₀ (hp s hs x)).mpr
      have hh := h.norm_coe_le_norm x
      have hh' : (h x)^2 ≤ ‖h‖^2 := by
        rw [Real.norm_eq_abs] at hh
        nlinarith [sq_abs (h x), abs_nonneg (h x), norm_nonneg h]
      nlinarith [(perturbation_bounds h hs x).1, sq_nonneg ‖h‖]))
    (integrable_const _)
    (ae_of_all _ (fun x s hs => by
      convert! ((((hasDerivAt_id s).mul_const (h x)).const_add 1).log (hp s hs x).ne').add_const 1 |>.mul_const (h x) using 1 <;> simp_all only [id_eq, one_mul, pow_one] <;> ring))
  simpa using H.2

lemma entropy_hessian {d : ℕ} (h : Space d) :
    deriv (deriv (fun t : ℝ => ∫ x, (1+t*h x)*Real.log (1+t*h x) ∂torusMeasure d)) 0 =
      ∫ x, (h x)^2 ∂torusMeasure d := by
  have he : deriv (fun t : ℝ => ∫ x, (1+t*h x)*Real.log (1+t*h x) ∂torusMeasure d) =ᶠ[𝓝 0]
      (fun t => ∫ x, (Real.log (1+t*h x)+1)*h x ∂torusMeasure d) := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
      (by change |(0:ℝ)| < 1/(2*(‖h‖+1)); simp only [abs_zero]; positivity)] with t ht
    exact (entropy_hasDerivAt h ht).deriv
  rw [he.deriv_eq]
  exact (entropy_second_hasDerivAt h).deriv

#print axioms entropy_hessian
end BecknerOnofri.HighDim.UniformEntropy
