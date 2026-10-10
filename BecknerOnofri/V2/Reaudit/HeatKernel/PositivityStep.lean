module

public import BecknerOnofri.V2.Reaudit.HeatKernel.MixedKernel
public import Legacy.BecknerOnofri.WeightedStrictComparison
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

/-! # The positivity step of the induction in `prop:cosine-all`, from heat kernels

Printed steps (eq. `inverse-heat`, `derivative-comparison-operators`,
`strict-derivative-spectral-radius`, `inductive-derivative-equation`,
`positive-neumann-inverse`):

1. the inverse power `B^{-s} = Γ(s)⁻¹ ∫_0^∞ t^{s-1} e^{-tB} dt` has the integral kernel
   `Γ(s)⁻¹ ∫_0^∞ t^{s-1} p_B(t;x,x') dt` (here: `mellin s (p_B(·;x,x'))`);
2. strictly positive heat kernels give a strictly positive kernel (`mellin_pos`), and a strict
   pointwise-in-`t` kernel inequality integrates to a strict inequality of the Mellin kernels
   (`mellin_lt`);
3. a nonnegative nonzero fixed vector `g = T_i g` of the weighted operator `T_i` of the
   first-derivative equation, a strictly positive kernel for `T_i`, and a strictly smaller
   nonnegative kernel for `T_α` give `‖T_α‖ < 1` and hence the positivity of the Neumann inverse
   `(I - T_α)^{-1} = ∑ T_α^j`: from `(I - T_α) v ≥ 0` conclude `v ≥ 0`.

Step 3 is the generic legacy theorem
`Legacy.BecknerOnofri.WeightedStrictComparison.nonnegative_of_residual` (a Schur-test version of
the printed Perron–Frobenius argument; this is **reused**, not reproved).  The theorem
`positivity_step` below is **conditional**: its hypotheses are exactly the unformalized inputs of
the printed proof (listed in the docstring), they are not axioms and are not proved here.
-/

noncomputable section
open Set MeasureTheory
open scoped Real
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri PositiveOperatorNeumann BoundedL2Multiplier

/-- The Mellin transform `∫_0^∞ t^{s-1}/Γ(s) · p(t) dt` (kernel of an inverse power). -/
def mellin (s : ℝ) (p : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ (s - 1) / Real.Gamma s * p t

theorem mellin_pos {s : ℝ} (hs : 0 < s) {p : ℝ → ℝ} (hpos : ∀ t, 0 < t → 0 < p t)
    (hint : IntegrableOn (fun t => t ^ (s - 1) / Real.Gamma s * p t) (Ioi 0)) :
    0 < mellin s p := by
  unfold mellin
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => t ^ (s - 1) / Real.Gamma s * p t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (mul_pos (div_pos (Real.rpow_pos_of_pos ht _) (Real.Gamma_pos_of_pos hs)) (hpos t ht)).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have : Ioi (0 : ℝ) ⊆ Function.support (fun t => t ^ (s - 1) / Real.Gamma s * p t) ∩ Ioi 0 := by
    intro t ht
    refine ⟨?_, ht⟩
    exact (mul_pos (div_pos (Real.rpow_pos_of_pos ht _) (Real.Gamma_pos_of_pos hs)) (hpos t ht)).ne'
  exact lt_of_lt_of_le (by simp) (measure_mono this)

theorem mellin_nonneg {s : ℝ} (hs : 0 < s) {p : ℝ → ℝ} (hp : ∀ t, 0 < t → 0 ≤ p t) :
    0 ≤ mellin s p := by
  unfold mellin
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (div_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.Gamma_pos_of_pos hs).le) (hp t ht)

theorem mellin_lt {s : ℝ} (hs : 0 < s) {p q : ℝ → ℝ} (hlt : ∀ t, 0 < t → q t < p t)
    (hq : IntegrableOn (fun t => t ^ (s - 1) / Real.Gamma s * q t) (Ioi 0))
    (hp : IntegrableOn (fun t => t ^ (s - 1) / Real.Gamma s * p t) (Ioi 0)) :
    mellin s q < mellin s p := by
  have h := mellin_pos hs (p := fun t => p t - q t) (fun t ht => sub_pos.mpr (hlt t ht)) (by
    have := hp.sub hq
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring)
  unfold mellin at h ⊢
  have e : (∫ t in Ioi (0 : ℝ), t ^ (s - 1) / Real.Gamma s * (p t - q t)) =
      (∫ t in Ioi (0 : ℝ), t ^ (s - 1) / Real.Gamma s * p t) -
        ∫ t in Ioi (0 : ℝ), t ^ (s - 1) / Real.Gamma s * q t := by
    rw [← integral_sub hp hq]
    congr 1; funext t; ring
  linarith

/-- The Mellin kernel of a family of kernels `p(t, ·)`. -/
def mellinKernel {X : Type*} (s : ℝ) (p : ℝ → X × X → ℝ) (z : X × X) : ℝ := mellin s (fun t => p t z)

section Step
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- **The positivity step of `prop:cosine-all`, from heat kernels (conditional).**

Data: a finite measure space `(X, μ)` (the unfolded domain `Ω_{e_i}`, on which the zero
extension of the `Ω_α`-objects lives), a bounded weight `w = √ρ > 0` a.e., a constant `c > 0`
(the constant `β c_d` of the manuscript) and an exponent `s > 0` (`s = d/2`), bounded operators
`T` (standing for `P_{D_i}^{-s}`) and `R` (standing for `B_α^{-s}`, extended by zero) on
`L²(μ)`, and heat-kernel families `pI` (of `P_{D_i}`) and `pB` (of `B_α`, extended by zero).

Hypotheses (the inputs of the printed proof; none is proved in this file):
* `hrepT`, `hrepR`: `T` and `R` are the integral operators with the Mellin kernels of `pI`, `pB`
  (`eq:inverse-heat`, spectral calculus for the Friedrichs operators);
* `hpos`, `hlt`, `hint*`: for almost every `z`, `pI(t,z) > 0` and `0 ≤ pB(t,z) < pI(t,z)` for all
  `t > 0` (`eq:dirichlet-heat-positive` and `eq:one-coordinate-strict-kernel` /
  `eq:several-coordinate-strict-kernel`; the strict inequalities there follow from the Dirichlet
  and reflection facts of `MixedKernel.lean` **and from the potential-domination
  `p_{B_α} ≤ p_{P_D}` of `eq:potential-kernel-domination`, which is itself unproved**), together
  with integrability of the Mellin integrands;
* `hsymI`, `hsymB`: symmetry of the kernels;
* `hcompact`: compactness of `R` (compact embedding of the form domain);
* `hg`: the first-derivative Euler equation `T_i g = g` with `g ≥ 0`, `g ≠ 0` (here
  `g = √ρ v_i`; `eq:first-derivative-euler`, Lemma `lem:fractional`).

Conclusion: `(I - T_α) v ≥ 0 ⟹ v ≥ 0`, i.e. positivity of the Neumann inverse
(`eq:positive-neumann-inverse`) with `T_α = c·w R w`. -/
theorem positivity_step (w : Weight μ) {c s : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hw : ∀ᵐ x ∂μ, 0 < w.value x) (T R : Operator μ)
    (pI pB : ℝ → X × X → ℝ)
    (hmI : AEStronglyMeasurable (mellinKernel s pI) (μ.prod μ))
    (hmB : AEStronglyMeasurable (mellinKernel s pB) (μ.prod μ))
    (hpos : ∀ᵐ z ∂μ.prod μ, ∀ t, 0 < t → 0 < pI t z)
    (hnn : ∀ᵐ z ∂μ.prod μ, ∀ t, 0 < t → 0 ≤ pB t z)
    (hlt : ∀ᵐ z ∂μ.prod μ, ∀ t, 0 < t → pB t z < pI t z)
    (hintI : ∀ᵐ z ∂μ.prod μ,
      IntegrableOn (fun t => t ^ (s - 1) / Real.Gamma s * pI t z) (Ioi 0))
    (hintB : ∀ᵐ z ∂μ.prod μ,
      IntegrableOn (fun t => t ^ (s - 1) / Real.Gamma s * pB t z) (Ioi 0))
    (hsymI : ∀ᵐ z ∂μ.prod μ, mellinKernel s pI z.swap = mellinKernel s pI z)
    (hsymB : ∀ᵐ z ∂μ.prod μ, mellinKernel s pB z.swap = mellinKernel s pB z)
    (hrepT : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => mellinKernel s pI (x, y) * f y) μ ∧
        (∫ y, mellinKernel s pI (x, y) * f y ∂μ) = T f x)
    (hrepR : ∀ f : RealL2 μ, ∀ᵐ x ∂μ,
      Integrable (fun y => mellinKernel s pB (x, y) * f y) μ ∧
        (∫ y, mellinKernel s pB (x, y) * f y ∂μ) = R f x)
    (hcompact : IsCompactOperator R)
    (g : RealL2 μ) (hg0 : Nonnegative μ g) (hgne : g ≠ 0) (hg : w.conjugate c T g = g)
    (v : RealL2 μ) (hv : Nonnegative μ (v - w.conjugate c R v)) : Nonnegative μ v := by
  refine WeightedStrictComparison.nonnegative_of_residual w hc hw T R
    (mellinKernel s pI) (mellinKernel s pB) hmI hmB ?_ ?_ ?_ hsymI hsymB hrepT hrepR hcompact g hg0
    hgne hg v hv
  · filter_upwards [hpos, hintI] with z hz hi
    exact mellin_pos hs hz hi
  · filter_upwards [hnn] with z hz
    exact mellin_nonneg hs hz
  · filter_upwards [hlt, hintI, hintB] with z hz hi hb
    exact mellin_lt hs hz hb hi

end Step

end BecknerOnofri.V2.Reaudit.HeatKernel
