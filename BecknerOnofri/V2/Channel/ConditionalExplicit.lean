module

public import BecknerOnofri.V2.Channel.ConditionalProfile
public import BecknerOnofri.V2.Channel.CircleFacts
public import BecknerOnofri.SmoothConditionalRegularity
public import BecknerOnofri.CircleMomentTransport
public import BecknerOnofri.CircleDensityParseval
public import BecknerOnofri.SpinBinaryCost
public import BecknerOnofri.V2.Circle.ExplicitCorrection

@[expose] public section

/-!
# Lemma 5.16 applied at every conditioning value (work package G10, part (c))

Source: proof of Proposition 5.12(i), from "The conditional densities are smooth, strictly positive,
and even in `x_i`" through `eq:section5-channel-one-coordinate-entropy`.

For `V ∈ C^∞([-1,1]^d)` with `∂_iV ≥ 0` and `ρ = e^{V(cos 2πx)}` smooth, the conditional density
`p_i(· | x_{<i})` of `x_i` is, for **every** value of the conditioning vector `x_{<i}` (we use the
prefix of `x`): strictly positive, even, `C^∞`, of mass one, a nondecreasing exponential of the
cosine coordinate, with first cosine moment `t_i ∈ [0,1)` obtained by pairing the cosine values
`±z`.  Lemma 5.16 (`circle_entropy_explicit`) then gives, for that conditioning value,
`Ent(p_i) ≥ 2 I_B(t_i) + ψ(t_i) + r_2²/40 + 2 r_3²/15 + (27/40) Σ_{n≥4} r_n²/n`.
No convexity of the logarithmic profile is used (neither `∂_i² V ≥ 0` nor the mixture).
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped ContDiff
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.HighDim.EntropyShearer

theorem rep_continuous {d : ℕ} {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    {f : Torus d → ℝ} (hrep : ∀ x, f x = Real.exp (V (cosineVector x))) : Continuous f := by
  have h := hc.comp_continuous (cosineVector_continuous d) (fun y => cosineVector_mem y)
  have he : f = fun y => Real.exp (V (cosineVector y)) := funext hrep
  rw [he]
  exact Real.continuous_exp.comp h

theorem rep_positiveBounded {d : ℕ} {V : (Fin d → ℝ) → ℝ} (hc : ContinuousOn V (cosineCube d))
    {f : Torus d → ℝ} (hrep : ∀ x, f x = Real.exp (V (cosineVector x))) : PositiveBounded f :=
  positiveBounded_of_continuous_pos (rep_continuous hc hrep) (fun y => by
    rw [hrep]; exact Real.exp_pos _)

/-- A function nondecreasing in each cosine coordinate (from `∂_iV ≥ 0`). -/
theorem rep_cosMonotone {d : ℕ} {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (h1 : ∀ v ∈ cosineCube d, ∀ i : Fin d, 0 ≤ cosinePartial i V v)
    {f : Torus d → ℝ} (hrep : ∀ x, f x = Real.exp (V (cosineVector x))) :
    ∀ (i : Fin d) (x : Torus d) (y z : UnitAddCircle), (fourier 1 y).re ≤ (fourier 1 z).re →
      f (update x i y) ≤ f (update x i z) := by
  intro i x y z h
  rw [hrep, hrep, cosineVector_update, cosineVector_update]
  apply Real.exp_le_exp.mpr
  have hy : (fourier 1 y).re ∈ Icc (-1 : ℝ) 1 := by
    have := cosineVector_mem (fun _ : Fin d => y); exact ⟨this.1 i, this.2 i⟩
  have hz : (fourier 1 z).re ∈ Icc (-1 : ℝ) 1 := by
    have := cosineVector_mem (fun _ : Fin d => z); exact ⟨this.1 i, this.2 i⟩
  exact CosineShape.coordinate_monotone hV i (fun v hv => h1 v hv i) (cosineVector_mem x) hy hz h

/-- **Lemma 5.16 at every conditioning value.**  For each `i` and each `x` (only `x_{<i}` matters):
the conditional first moment lies in `[0,1)`, the series of higher moments is summable, and
`Ent(p_i(·|x_{<i})) ≥ 2 I_B(t_i) + ψ(t_i) + r_{i,2}²/40 + 2 r_{i,3}²/15 + (27/40) Σ_{n≥4} r_{i,n}²/n`. -/
theorem conditional_explicit {d : ℕ} {V : (Fin d → ℝ) → ℝ} (hV : ContDiffOn ℝ ∞ V (cosineCube d))
    (h1 : ∀ v ∈ cosineCube d, ∀ i : Fin d, 0 ≤ cosinePartial i V v)
    {f : Torus d → ℝ} (hrep : ∀ x, f x = Real.exp (V (cosineVector x))) (hs : SmoothOnTorus f)
    (i : Fin d) (x : Torus d) :
    0 ≤ conditionalCosineMoment f i 1 x ∧ conditionalCosineMoment f i 1 x < 1 ∧
    Summable (fun n : ℕ => (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) ∧
    2 * Spin.binaryCost (conditionalCosineMoment f i 1 x) +
      BecknerOnofri.V2.Circle.psi (conditionalCosineMoment f i 1 x) +
      (1 / 40) * (conditionalCosineMoment f i 2 x) ^ 2 +
      (2 / 15) * (conditionalCosineMoment f i 3 x) ^ 2 +
      (27 / 40) * (∑' n : ℕ, (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) ≤
        conditionalEntropy f i x := by
  have hc := hV.continuousOn
  obtain ⟨F, hcF, hmF, hprofile⟩ := conditional_log_profile_mono hV h1 f hrep i x
  have hfpos : PositiveBounded f := rep_positiveBounded hc hrep
  let a : UnitAddCircle → ℝ := conditionalDensity f i x
  have hcos_mem (z : UnitAddCircle) : (fourier 1 z).re ∈ Icc (-1 : ℝ) 1 := by
    have h := cosineVector_mem (fun _ : Fin d => z); exact ⟨h.1 i, h.2 i⟩
  have ha_cont : Continuous a := by
    have : a = fun z => Real.exp (F (fourier 1 z).re) := funext hprofile
    rw [this]
    exact Real.continuous_exp.comp (hcF.comp_continuous cosine_continuous hcos_mem)
  have ha_pos : ∀ z, 0 < a z := conditional_density_positive hfpos i x
  have ha_int : (∫ z, a z ∂AddCircle.haarAddCircle) = 1 := conditional_density_mass hfpos i x
  let p : Torus 1 → ℝ := fun z => conditionalDensity f i x (z 0)
  have hp : Continuous p := ha_cont.comp (continuous_apply 0)
  have hm : (∫ z, p z ∂torusMeasure 1) = 1 := by
    rw [CirclePoisson.integral_torus_circle]
    exact ha_int
  have hmom (n : ℕ) : CirclePoisson.moment p n = conditionalCosineMoment f i n x :=
    CirclePoisson.moment_eq_cosine_integral p hp n
  have heven : ∀ z, p (-z) = p z := by
    intro z
    dsimp only [p]
    rw [hprofile, hprofile]
    simp only [Pi.neg_apply, fourier_apply, zsmul_neg, AddCircle.toCircle_neg]
    simp
  have hreg : ContDiff ℝ 3 (fun t : ℝ => p (fun _ => (t : UnitAddCircle))) :=
    (smooth_conditional_density f hs i x).of_le (WithTop.coe_le_coe.mpr (le_top : (3 : ℕ∞) ≤ ⊤))
  -- first moment in [0,1)
  have hmono : ∀ y z : UnitAddCircle, (fourier 1 y).re ≤ (fourier 1 z).re → a y ≤ a z := by
    intro y z h
    change conditionalDensity f i x y ≤ conditionalDensity f i x z
    rw [hprofile, hprofile]
    exact Real.exp_le_exp.mpr (hmF (hcos_mem y) (hcos_mem z) h)
  have ht0 : 0 ≤ conditionalCosineMoment f i 1 x := by
    have h := integral_mul_cos_nonneg (conditional_density_integrable hfpos i x) hmono
    simpa only [conditionalCosineMoment, Nat.cast_one] using h
  have ht1 : conditionalCosineMoment f i 1 x < 1 := by
    have h := integral_density_cos_lt_one ha_cont ha_pos ha_int
    simpa only [conditionalCosineMoment, Nat.cast_one] using h
  -- summability of the higher moments through Parseval
  have hsum := (CircleOuter.density_parseval p hp heven hm).1
  have hs' : Summable (fun n : ℕ => (conditionalCosineMoment f i (n + 1) x) ^ 2) := by
    simpa only [← hmom, CirclePoisson.moment, Nat.cast_add, Nat.cast_one] using hsum
  have hs4 : Summable (fun n : ℕ => (conditionalCosineMoment f i (n + 4) x) ^ 2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 3).mpr hs'
  have hs4' : Summable (fun n : ℕ => (conditionalCosineMoment f i (n + 4) x) ^ 2 / ((n : ℝ) + 4)) := by
    apply hs4.of_nonneg_of_le (fun n => by positivity)
    intro n
    exact div_le_self (sq_nonneg _) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  refine ⟨ht0, ht1, hs4', ?_⟩
  have h := BecknerOnofri.V2.Circle.circle_entropy_explicit p hp (fun z => ha_pos (z 0)) heven hm hreg
    (by rw [hmom]; exact ht0)
  simpa only [hmom, CirclePoisson.integral_torus_circle, p, conditionalEntropy] using h

end BecknerOnofri.V2.Channel
