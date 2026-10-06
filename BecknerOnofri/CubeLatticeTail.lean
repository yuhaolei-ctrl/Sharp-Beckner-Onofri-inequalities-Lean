module

public import BecknerOnofri.IterationOmittedTail
public import BecknerOnofri.SpectralSlice
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! Explicit analytic bounds for the omitted lattice tail outside a cube.
The estimates use the actual Gaussian lattice sum and gamma integrals. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.CubeLatticeTail
open Legacy.BecknerOnofri.ThetaDomination

/-- An even decreasing nonnegative lattice sum is bounded by the value at zero
plus twice its integral on the positive half-line. -/
theorem even_lattice_sum_le {f : ℝ → ℝ} (heven : Function.Even f)
    (hanti : AntitoneOn f (Ici 0)) (hint : IntegrableOn f (Ioi 0))
    (hnonneg : ∀ x ∈ Ioi 0, 0 ≤ f x) :
    (∑' n : ℤ, f n) ≤ f 0 + 2 * ∫ x in Ioi 0, f x := by
  have heven' (x : ℝ) : f (-x)=f x := heven x
  have hs := hanti.summable_of_integrableOn_Ioi_zero hint hnonneg
  have hs' : Summable (fun n : ℕ => f (-(n+1 : ℤ))) := by
    simpa only [Int.cast_neg,heven',Nat.cast_add,Nat.cast_one,Int.cast_add,
      Int.cast_natCast,Int.cast_one] using (summable_nat_add_iff 1).mpr hs
  rw [tsum_of_nat_of_neg_add_one (by simpa using hs) (by simpa only [Int.cast_neg] using hs')]
  simp only [Int.cast_neg,heven',Int.cast_add,Int.cast_natCast,Int.cast_one]
  have htail := hanti.tsum_add_one_le_integral hint hnonneg
  have heq := hs.tsum_eq_zero_add
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero] at heq htail
  linarith

/-- The exact elementary theta estimate underlying every transverse-coordinate bound. -/
theorem realTheta_le {t : ℝ} (ht : 0 < t) :
    realTheta t ≤ 1 + Real.sqrt (Real.pi / t) := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-t*x^2)) (Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hx hxy 2) (neg_nonpos.mpr ht.le)
  have h := even_lattice_sum_le (f := fun x : ℝ => Real.exp (-t*x^2))
    (by intro x; simp) hanti (integrable_exp_neg_mul_sq ht).integrableOn
    (by intro x hx; positivity)
  simpa only [realTheta,zero_pow (by decide : 2≠0),mul_zero,Real.exp_zero,
    integral_gaussian_Ioi,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using h

/-- The first term plus integral bound used after the transverse Gaussian integration. -/
theorem power_tail_le {a : ℝ} (ha : a < -1) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℕ, ((n+N:ℕ):ℝ)^a) ≤
      (N:ℝ)^a + (N:ℝ)^(a+1)/(-a-1) := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x^a) (Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN0.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt ha hN0
  have hs := hanti.summable_of_integrableOn_Ioi hint
    (by intro x hx; exact Real.rpow_nonneg (hN0.trans hx).le _)
  have htail := hanti.tsum_comp_add_le_integral N hint
    (by intro x hx; exact Real.rpow_nonneg (hN0.trans hx).le _)
  have hsN := (summable_nat_add_iff N).mpr hs
  rw [hsN.tsum_eq_zero_add]
  simp only [zero_add]
  have he : (∑' n : ℕ, ((n+1+N:ℕ):ℝ)^a) =
      ∑' n : ℕ, ((n+N+1:ℕ):ℝ)^a := by congr 1; ext n; congr 2; omega
  rw [he]
  rw [integral_Ioi_rpow_of_lt ha hN0] at htail
  have hr : -(N:ℝ)^(a+1)/(a+1) = (N:ℝ)^(a+1)/(-a-1) := by
    rw [show -a-1=-(a+1) by ring,div_neg,neg_div]
  linarith

#print axioms realTheta_le
#print axioms power_tail_le
end BecknerOnofri.HighDim.CubeLatticeTail
