module

public import BecknerOnofri.V2.Reaudit.HeatKernel.ResolventStrong
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-! # Heat-semigroup comparison for `B_m` from the resolvent comparison (U05/S015, step 4)

Printed step: `0 ≤ p_B ≤ p_{P_D}` (Trotter product formula + monotone convergence of forms).
Here: the exponential formula `e^{-tA} = lim_n (1 + tA/n)^{-n}`, applied coefficientwise in the
eigenbasis (`dg_tendsto`), together with the resolvent comparison (`ResolventStrong`) and
monotonicity of powers of positive operators, gives for `f ≥ 0`, `t > 0`:

`0 ≤ e^{-tB_m} f ≤ e^{-m(m-1)t} e^{-tP_D} f`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann Legacy.BecknerOnofri.BoundedL2Multiplier

/-! ### Powers of ordered positive operators -/

theorem pow_compare (A B : Operator intervalMeasure)
    (hA : ∀ f : JacobiL2, 0 ≤ f → 0 ≤ A f) (hAB : ∀ f : JacobiL2, 0 ≤ f → A f ≤ B f) (n : ℕ) :
    ∀ f : JacobiL2, 0 ≤ f → 0 ≤ (A ^ n) f ∧ (A ^ n) f ≤ (B ^ n) f := by
  have hB : ∀ f : JacobiL2, 0 ≤ f → 0 ≤ B f := fun f hf => (hA f hf).trans (hAB f hf)
  induction n with
  | zero => intro f hf; simp [hf]
  | succ n ih =>
    intro f hf
    obtain ⟨h1, h2⟩ := ih f hf
    rw [pow_succ', pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
    refine ⟨hA _ h1, (hAB _ h1).trans ?_⟩
    have := hB _ (sub_nonneg.mpr h2)
    rw [map_sub] at this
    exact sub_nonneg.mp this

/-! ### Exponential formula for diagonal operators -/

theorem tendsto_resolvent_symbol {l : ℝ} (hl : 0 ≤ l) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => ((1 + t * l / ((n : ℝ) + 1)) ^ (n + 1))⁻¹) atTop
      (𝓝 (Real.exp (-t * l))) := by
  have h := Real.tendsto_one_add_div_pow_exp (t * l)
  have h2 := (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (1 + t * l / (n : ℝ)) ^ n) 1).mpr h
  have h3 := h2.inv₀ (Real.exp_pos _).ne'
  rw [show -t * l = -(t * l) by ring, Real.exp_neg]
  simpa [Nat.cast_add, Nat.cast_one] using h3

theorem abs_symbol_le {l : ℝ} (hl : 0 ≤ l) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    |((1 + t * l / ((n : ℝ) + 1)) ^ (n + 1))⁻¹| ≤ 1 := by
  have h0 : 1 ≤ 1 + t * l / ((n : ℝ) + 1) := by
    have : 0 ≤ t * l / ((n : ℝ) + 1) := by positivity
    linarith
  have h1 : 1 ≤ (1 + t * l / ((n : ℝ) + 1)) ^ (n + 1) := one_le_pow₀ h0
  rw [abs_of_pos (inv_pos.mpr (by linarith))]
  exact inv_le_one_of_one_le₀ h1

theorem dg_exp_formula {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : HilbertBasis ι ℝ H) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ}
    (ht : 0 < t) (u : H) :
    Tendsto (fun n : ℕ => dg e (fun i => ((1 + t * lam i / ((n : ℝ) + 1)) ^ (n + 1))⁻¹) u)
      atTop (𝓝 (dg e (fun i => Real.exp (-t * lam i)) u)) := by
  refine dg_tendsto e (M := 1) (fun n i => abs_symbol_le (hlam i) ht n) (fun i => ?_)
    (fun i => tendsto_resolvent_symbol (hlam i) ht) u
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [hlam i]

/-- `(ν (A+ν)^{-1})^{n+1}` with `ν = (n+1)/t` is the diagonal operator with symbol
`(1 + tλ/(n+1))^{-(n+1)}`. -/
theorem smul_dg_pow {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : HilbertBasis ι ℝ H) {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i) {t : ℝ}
    (ht : 0 < t) (n : ℕ) :
    ((((n : ℝ) + 1) / t) • dg e (fun i => (lam i + ((n : ℝ) + 1) / t)⁻¹)) ^ (n + 1) =
      dg e (fun i => ((1 + t * lam i / ((n : ℝ) + 1)) ^ (n + 1))⁻¹) := by
  have hν : 0 < ((n : ℝ) + 1) / t := by positivity
  have hb : Bdd (fun i => (lam i + ((n : ℝ) + 1) / t)⁻¹) := by
    refine ⟨(((n : ℝ) + 1) / t)⁻¹, fun i => ?_⟩
    have h0 : 0 < lam i + ((n : ℝ) + 1) / t := by linarith [hlam i]
    rw [abs_of_pos (inv_pos.mpr h0)]
    exact inv_anti₀ hν (by linarith [hlam i])
  have hs : ((((n : ℝ) + 1) / t) • dg e (fun i => (lam i + ((n : ℝ) + 1) / t)⁻¹)) =
      dg e (fun i => (((n : ℝ) + 1) / t) * (lam i + ((n : ℝ) + 1) / t)⁻¹) := by
    ext u : 1
    exact dg_smul e hb _ u
  have hb2 : Bdd (fun i => (((n : ℝ) + 1) / t) * (lam i + ((n : ℝ) + 1) / t)⁻¹) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨|((n : ℝ) + 1) / t| * M, fun i => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)
  rw [hs, dg_pow e hb2]
  congr 1
  funext i
  have h0 : 0 < lam i + ((n : ℝ) + 1) / t := by linarith [hlam i]
  have h1 : (((n : ℝ) + 1) / t) * (lam i + ((n : ℝ) + 1) / t)⁻¹ =
      (1 + t * lam i / ((n : ℝ) + 1))⁻¹ := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
    ring
  rw [h1, inv_pow]

theorem smul_nonneg_L2 {a : ℝ} (ha : 0 ≤ a) {x : JacobiL2} (hx : 0 ≤ x) : 0 ≤ a • x := by
  apply (nonnegative_iff intervalMeasure _).mp
  have hx' := (nonnegative_iff intervalMeasure _).mpr hx
  filter_upwards [hx', Lp.coeFn_smul a x] with y h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg ha h1

theorem smul_le_smul_L2 {a : ℝ} (ha : 0 ≤ a) {x y : JacobiL2} (h : x ≤ y) : a • x ≤ a • y := by
  have := smul_nonneg_L2 ha (sub_nonneg.mpr h)
  rw [smul_sub] at this
  exact sub_nonneg.mp this

/-! ### The comparison -/

theorem dg_resolvent_eq {m : ℕ} (hm : 0 < m) (ν : ℝ) :
    resOp hm ν = dg (hilbertBasis hm) (fun i => (eigenvalue m i + ν)⁻¹) := rfl

theorem S_eq_dg {m : ℕ} (ν : ℝ) :
    S (ν + cc m) = dg (hilbertBasis (one_pos : 0 < 1))
      (fun i => ((eigenvalue 1 i + cc m) + ν)⁻¹) := by
  show dg _ (resSym 1 (ν + cc m)) = _
  congr 1
  funext i
  simp only [resSym]
  ring_nf

theorem heatOp_eq_limit {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (u : JacobiL2) :
    Tendsto (fun n : ℕ => ((((n : ℝ) + 1) / t) • resOp hm (((n : ℝ) + 1) / t)) ^ (n + 1) $ u)
      atTop (𝓝 (heatOp hm t u)) := by
  have := dg_exp_formula (hilbertBasis hm) (lam := fun i => eigenvalue m i)
    (fun i => eigenvalue_nonneg' m i) ht u
  have e : ∀ n : ℕ, ((((n : ℝ) + 1) / t) • resOp hm (((n : ℝ) + 1) / t)) ^ (n + 1) =
      dg (hilbertBasis hm) (fun i => ((1 + t * eigenvalue m i / ((n : ℝ) + 1)) ^ (n + 1))⁻¹) :=
    fun n => smul_dg_pow (hilbertBasis hm) (lam := fun i => eigenvalue m i)
      (fun i => eigenvalue_nonneg' m i) ht n
  simp only [e]
  exact this

theorem shifted_limit {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (u : JacobiL2) :
    Tendsto (fun n : ℕ => ((((n : ℝ) + 1) / t) • S ((((n : ℝ) + 1) / t) + cc m)) ^ (n + 1) $ u)
      atTop (𝓝 (Real.exp (-(cc m) * t) • heatOp one_pos t u)) := by
  have hc := cc_nonneg hm
  have hl : ∀ i, 0 ≤ eigenvalue 1 i + cc m := fun i => by linarith [eigenvalue_nonneg' 1 i]
  have := dg_exp_formula (hilbertBasis (one_pos : 0 < 1)) (lam := fun i => eigenvalue 1 i + cc m)
    hl ht u
  have e : ∀ n : ℕ, ((((n : ℝ) + 1) / t) • S ((((n : ℝ) + 1) / t) + cc m)) ^ (n + 1) =
      dg (hilbertBasis (one_pos : 0 < 1))
        (fun i => ((1 + t * (eigenvalue 1 i + cc m) / ((n : ℝ) + 1)) ^ (n + 1))⁻¹) := by
    intro n
    rw [S_eq_dg]
    exact smul_dg_pow (hilbertBasis (one_pos : 0 < 1)) (lam := fun i => eigenvalue 1 i + cc m)
      hl ht n
  simp only [e]
  have e2 : dg (hilbertBasis (one_pos : 0 < 1)) (fun i => Real.exp (-t * (eigenvalue 1 i + cc m))) u =
      Real.exp (-(cc m) * t) • heatOp one_pos t u := by
    rw [heatOp, dg_smul _ (bdd_heatSym ht.le)]
    have hf : (fun i => Real.exp (-t * (eigenvalue 1 i + cc m))) =
        fun i => Real.exp (-(cc m) * t) * heatSym 1 t i := by
      funext i
      simp only [heatSym]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hf]
  rw [← e2]
  exact this

/-- `e^{-tB_m} f ≥ 0` for `f ≥ 0`. -/
theorem heatOp_nonneg {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) {f : JacobiL2} (hf : 0 ≤ f) :
    0 ≤ heatOp hm t f := by
  refine ge_of_tendsto' (heatOp_eq_limit hm ht f) (fun n => ?_)
  have hν : 0 < ((n : ℝ) + 1) / t := by positivity
  have := (pow_compare ((((n : ℝ) + 1) / t) • resOp hm (((n : ℝ) + 1) / t))
    ((((n : ℝ) + 1) / t) • S ((((n : ℝ) + 1) / t) + cc m))
    (fun g hg => by
      rw [smul_apply]
      exact smul_nonneg_L2 hν.le (resOp_nonneg hm hν hg))
    (fun g hg => by
      rw [smul_apply, smul_apply]
      exact smul_le_smul_L2 hν.le (resOp_le hm hν hg)) (n + 1) f hf).1
  exact this

/-- **Heat-semigroup domination**: `e^{-tB_m} f ≤ e^{-m(m-1)t} e^{-tP_D} f` for `f ≥ 0`. -/
theorem heatOp_le {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) {f : JacobiL2} (hf : 0 ≤ f) :
    heatOp hm t f ≤ Real.exp (-(cc m) * t) • heatOp one_pos t f := by
  refine le_of_tendsto_of_tendsto' (heatOp_eq_limit hm ht f) (shifted_limit hm ht f)
    (fun n => ?_)
  have hν : 0 < ((n : ℝ) + 1) / t := by positivity
  exact (pow_compare ((((n : ℝ) + 1) / t) • resOp hm (((n : ℝ) + 1) / t))
    ((((n : ℝ) + 1) / t) • S ((((n : ℝ) + 1) / t) + cc m))
    (fun g hg => by
      rw [smul_apply]
      exact smul_nonneg_L2 hν.le (resOp_nonneg hm hν hg))
    (fun g hg => by
      rw [smul_apply, smul_apply]
      exact smul_le_smul_L2 hν.le (resOp_le hm hν hg)) (n + 1) f hf).2

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
