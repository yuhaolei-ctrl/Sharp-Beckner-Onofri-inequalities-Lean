module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Expansion

@[expose] public section

/-! # Uniform quadratic bound for the `H^s` graph near `(1, 0)`

`Branch.graph_quadratic` only gives `w(τ, z) = O(‖z‖² + |τ-1| ‖z‖)`.  For the parameter dependence
of the reduced functional (`Parameter.lean`) a bound `w(τ,z) = O(‖z‖²)` *uniform in `τ`* is needed.
It is obtained here natively from the complement equation: with `e = Id - P_{K^⊥}T` (invertible on
`K^⊥ ⊂ H^s`, `HsC.equiv`),

`e w = (τ-1) P_{K^⊥}T w + τ (½ P_{K^⊥}T v² + P_{K^⊥}T (v w + ½ w² + R_3(v+w)))`

(`equiv_graph`), so that `‖w‖ ≤ ε ‖w‖ + B ‖z‖²` with `ε → 0` as `(τ, z) → (1, 0)`; absorbing
`ε ‖w‖` gives `‖w‖ ≤ 2B‖z‖²`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-- The complement equation at arbitrary `τ`, written with `e = Id - P_{K^⊥}T`:
`e w = (τ-1) P_{K^⊥}T w + τ (½ P_{K^⊥}T v² + P_{K^⊥}T (v w + ½ w² + R_3(v+w)))`. -/
theorem equiv_graph (hd11 : 11 ≤ d) (τ : ℝ) (z : Coordinates d) (w : HsC d s)
    (hsol : complementEq d s τ z w = 0) :
    HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num) w =
      (τ - 1) • HsC.linearPart d s w + τ • (quadraticSourceH d s z +
        cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
          gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s)))) := by
  set v : Hs d s := Hs.assemblyH d s z with hv
  set U : Hs d s := v + (w : Hs d s) with hU
  have hw : w = τ • cmG d s (Hs.gibbs U - 1) := by
    unfold complementEq at hsol
    rw [Hs.reconstructionH_apply, sub_eq_zero] at hsol
    exact hsol
  have hdec : Hs.gibbs U - 1 = U + (1 / 2 : ℝ) • (U ^ 2 - pk d s 2 U • (1 : Hs d s)) + gibbsRem3 U := by
    unfold gibbsRem3
    abel
  have hsq : U ^ 2 = v ^ 2 + v * (w : Hs d s) + v * (w : Hs d s) + (w : Hs d s) ^ 2 := by
    rw [hU]; ring
  have hcU : cmG d s U = HsC.linearPart d s w := by
    rw [hU, map_add, hv, cmG_assemblyH, zero_add, cmG_coe]
  have hcU2 : cmG d s (U ^ 2) = cmG d s (v ^ 2) + cmG d s (v * (w : Hs d s)) +
      cmG d s (v * (w : Hs d s)) + cmG d s ((w : Hs d s) ^ 2) := by
    rw [hsq]; simp only [map_add]
  have hcg : cmG d s (Hs.gibbs U - 1) = HsC.linearPart d s w + (1 / 2 : ℝ) • cmG d s (v ^ 2) +
      cmG d s (v * (w : Hs d s)) + (1 / 2 : ℝ) • cmG d s ((w : Hs d s) ^ 2) +
        cmG d s (gibbsRem3 U) := by
    rw [hdec]
    simp only [map_add, map_smul, map_sub, hcU, hcU2, cmG_one, smul_zero, sub_zero]
    module
  rw [HsC.equiv_apply, one_smul]
  have e1 : w = τ • (HsC.linearPart d s w + (1 / 2 : ℝ) • cmG d s (v ^ 2) +
      cmG d s (v * (w : Hs d s)) + (1 / 2 : ℝ) • cmG d s ((w : Hs d s) ^ 2) +
        cmG d s (gibbsRem3 U)) := by
    rw [← hcg]; exact hw
  simp only [quadraticSourceH, map_add, map_smul]
  nth_rewrite 1 [e1]
  module

/-- The absorption step, in plain real arithmetic. -/
theorem absorb_real {K Ln Lc C a b t τ R : ℝ} (hK : 0 ≤ K) (hLn : 0 ≤ Ln) (hLc : 0 ≤ Lc)
    (hC : 0 ≤ C) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ht : 0 ≤ t) (hτ : |τ| ≤ 2) (hR0 : 0 ≤ R)
    (hR : R ≤ C * (a + b) ^ 3) (ha : a ≤ 1) (hb : b ≤ 1)
    (hη : K * t * Ln + 2 * K * Lc * (a + (1 / 2 + 4 * C) * b) ≤ 1 / 2)
    (h : b ≤ K * (t * (Ln * b) + |τ| * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R)))) :
    b ≤ 2 * (2 * K * Lc * (1 / 2 + 4 * C)) * a ^ 2 := by
  have h3 : (a + b) ^ 3 ≤ 4 * (a ^ 2 + b ^ 2) := by
    have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
    have : (a + b) ^ 3 = (a + b) * (a + b) ^ 2 := by ring
    rw [this]
    have hab : a + b ≤ 2 := by linarith
    calc (a + b) * (a + b) ^ 2 ≤ 2 * (a + b) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hab (sq_nonneg _)
      _ ≤ 2 * (2 * (a ^ 2 + b ^ 2)) := by linarith
      _ = 4 * (a ^ 2 + b ^ 2) := by ring
  have hR' : R ≤ 4 * C * (a ^ 2 + b ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  have hinner : 0 ≤ Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R) := by positivity
  have hτ' : |τ| * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R)) ≤
      2 * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + 4 * C * (a ^ 2 + b ^ 2))) := by
    calc _ ≤ 2 * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R)) :=
          mul_le_mul_of_nonneg_right hτ hinner
      _ ≤ _ := by
        have : Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R) ≤
            Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + 4 * C * (a ^ 2 + b ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) hLc
        linarith
  have h4 : b ≤ K * (t * (Ln * b)) + K * (2 * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 +
      4 * C * (a ^ 2 + b ^ 2)))) := by
    calc b ≤ K * (t * (Ln * b) + |τ| * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 + R))) := h
      _ ≤ K * (t * (Ln * b) + 2 * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 +
          4 * C * (a ^ 2 + b ^ 2)))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        linarith
      _ = _ := by ring
  have h5 : K * (t * (Ln * b)) + K * (2 * (Lc * (a ^ 2 / 2 + a * b + b ^ 2 / 2 +
      4 * C * (a ^ 2 + b ^ 2)))) =
      b * (K * t * Ln + 2 * K * Lc * (a + (1 / 2 + 4 * C) * b)) +
        (2 * K * Lc * (1 / 2 + 4 * C)) * a ^ 2 := by ring
  rw [h5] at h4
  have h6 : b * (K * t * Ln + 2 * K * Lc * (a + (1 / 2 + 4 * C) * b)) ≤ b * (1 / 2) :=
    mul_le_mul_of_nonneg_left hη hb0
  nlinarith

/-- The map `x ↦ v(z) + w(τ,z)` tends to `0` through mean-zero elements. -/
def wX (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) : Hs d s := ((graph (s := s) hd11 x : HsC d s) : Hs d s)

def UX (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) : Hs d s :=
  Hs.reconstructionH d s (x.2, graph (s := s) hd11 x)

theorem UX_eq (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) :
    UX (s := s) hd11 x = Hs.assemblyH d s x.2 + wX hd11 x := rfl

theorem graph_tendsto_zero (hd11 : 11 ≤ d) :
    Tendsto (fun x : ℝ × Coordinates d => graph (s := s) hd11 x) (𝓝 (1, 0)) (𝓝 0) := by
  have := (graph_analytic (s := s) hd11).continuousAt.tendsto
  rwa [graph_base] at this

theorem wX_tendsto (hd11 : 11 ≤ d) :
    Tendsto (fun x : ℝ × Coordinates d => wX (s := s) hd11 x) (𝓝 (1, 0)) (𝓝 0) := by
  have h := ((HsC d s).subtypeL.continuous.tendsto (0 : HsC d s)).comp (graph_tendsto_zero (s := s) hd11)
  have h' : Tendsto (fun x : ℝ × Coordinates d => ((graph (s := s) hd11 x : HsC d s) : Hs d s))
      (𝓝 (1, 0)) (𝓝 0) := by simpa [Function.comp_def] using h
  exact h'

theorem UX_tendsto (hd11 : 11 ≤ d) :
    Tendsto (fun x : ℝ × Coordinates d => UX (s := s) hd11 x) (𝓝 (1, 0)) (meanZeroNhds d s) := by
  have h0 : Tendsto (fun x : ℝ × Coordinates d => UX (s := s) hd11 x) (𝓝 (1, 0)) (𝓝 0) := by
    have := ((Hs.reconstructionH d s).continuous.tendsto (0, 0)).comp
      ((continuous_snd.continuousAt (x := ((1 : ℝ), (0 : Coordinates d)))).tendsto.prodMk_nhds
        (graph_tendsto_zero (s := s) hd11))
    rw [show ((0 : Coordinates d), (0 : HsC d s)) = 0 from rfl, map_zero] at this
    exact this
  exact tendsto_nhdsWithin_iff.mpr ⟨h0, Eventually.of_forall fun x => Hs.meanCLM_reconstructionH _⟩

theorem assemblyH_norm_le (z : Coordinates d) : ‖Hs.assemblyH d s z‖ ≤ ‖Hs.assemblyH d s‖ * ‖z‖ :=
  (Hs.assemblyH d s).le_opNorm z

/-- The operator-norm constants entering the absorption argument. -/
def Kconst (hd11 : 11 ≤ d) : ℝ :=
  ‖((HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm : HsC d s →L[ℝ] HsC d s)‖

/-- The pointwise norm inequality extracted from `equiv_graph`:
`‖w‖ ≤ K (|τ-1| ‖T_c‖ ‖w‖ + |τ| ‖P T‖ (½‖v‖² + ‖v‖‖w‖ + ½‖w‖² + ‖R_3(v+w)‖))`. -/
theorem graph_norm_bound (hd11 : 11 ≤ d) (τ : ℝ) (z : Coordinates d) (w : HsC d s)
    (hsol : complementEq d s τ z w = 0) :
    ‖w‖ ≤ Kconst (s := s) hd11 * (|τ - 1| * (‖HsC.linearPart d s‖ * ‖w‖) +
      |τ| * (‖cmG d s‖ * (‖Hs.assemblyH d s z‖ ^ 2 / 2 + ‖Hs.assemblyH d s z‖ * ‖w‖ + ‖w‖ ^ 2 / 2 +
        ‖gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))‖))) := by
  have hEq := equiv_graph (s := s) hd11 τ z w hsol
  have hwe : w = (HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm
      ((τ - 1) • HsC.linearPart d s w + τ • (quadraticSourceH d s z +
        cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
          gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))))) := by
    rw [← hEq]; exact ((HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm_apply_apply w).symm
  have hK0 : 0 ≤ Kconst (s := s) hd11 := ContinuousLinearMap.opNorm_nonneg _
  have hLc0 : 0 ≤ ‖cmG d s‖ := ContinuousLinearMap.opNorm_nonneg _
  have h1 : ‖(Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
        gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s)))‖ ≤
      ‖Hs.assemblyH d s z‖ * ‖w‖ + ‖w‖ ^ 2 / 2 + ‖gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))‖ := by
    refine (norm_add₃_le).trans ?_
    have e1 : ‖Hs.assemblyH d s z * (w : Hs d s)‖ ≤ ‖Hs.assemblyH d s z‖ * ‖w‖ := norm_mul_le _ _
    have e2 : ‖(1 / 2 : ℝ) • (w : Hs d s) ^ 2‖ ≤ ‖w‖ ^ 2 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := norm_pow_le' (w : Hs d s) (by norm_num : 0 < 2)
      have h2 : ‖(w : Hs d s)‖ = ‖w‖ := rfl
      rw [h2] at this
      linarith
    linarith
  have hN : ‖cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
        gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s)))‖ ≤ ‖cmG d s‖ *
      (‖Hs.assemblyH d s z‖ * ‖w‖ + ‖w‖ ^ 2 / 2 + ‖gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))‖) :=
    ((cmG d s).le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 hLc0)
  have hQ : ‖quadraticSourceH d s z‖ ≤ ‖cmG d s‖ * (‖Hs.assemblyH d s z‖ ^ 2 / 2) := by
    unfold quadraticSourceH
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h2 : ‖cmG d s ((Hs.assemblyH d s z) ^ 2)‖ ≤ ‖cmG d s‖ * ‖Hs.assemblyH d s z‖ ^ 2 :=
      ((cmG d s).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_pow_le' _ (by norm_num : 0 < 2)) hLc0)
    linarith
  have hlin : ‖(τ - 1) • HsC.linearPart d s w‖ ≤ |τ - 1| * (‖HsC.linearPart d s‖ * ‖w‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((HsC.linearPart d s).le_opNorm w) (abs_nonneg _)
  have hrest : ‖τ • (quadraticSourceH d s z +
        cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
          gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))))‖ ≤
      |τ| * (‖cmG d s‖ * (‖Hs.assemblyH d s z‖ ^ 2 / 2 + ‖Hs.assemblyH d s z‖ * ‖w‖ + ‖w‖ ^ 2 / 2 +
        ‖gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))‖)) := by
    rw [norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    refine (norm_add_le _ _).trans ?_
    nlinarith [hQ, hN]
  calc ‖w‖ = ‖(HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm
        ((τ - 1) • HsC.linearPart d s w + τ • (quadraticSourceH d s z +
          cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
            gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s)))))‖ := by
        conv_lhs => rw [hwe]
    _ ≤ Kconst (s := s) hd11 * ‖(τ - 1) • HsC.linearPart d s w + τ • (quadraticSourceH d s z +
          cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
            gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))))‖ :=
        ((HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm :
          HsC d s →L[ℝ] HsC d s).le_opNorm _
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hK0
        exact (norm_add_le _ _).trans (add_le_add hlin hrest)

/-- **Uniform quadratic bound** `w(τ, z) = O(‖z‖²)` as `(τ, z) → (1, 0)` (native in `H^s`; the
parameter-uniform strengthening of `graph_quadratic`). -/
theorem graph_uniform (hd11 : 11 ≤ d) :
    (fun x : ℝ × Coordinates d => graph (s := s) hd11 x) =O[𝓝 (1, (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 2) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Kconst (s := s) hd11 := ⟨_, rfl⟩
  obtain ⟨Ln, hLn⟩ : ∃ Ln : ℝ, Ln = ‖HsC.linearPart d s‖ := ⟨_, rfl⟩
  obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = ‖cmG d s‖ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖Hs.assemblyH d s‖ := ⟨_, rfl⟩
  -- the cubic remainder
  obtain ⟨C, hC0⟩ := ((gibbs_second_order (d := d) (s := s)).comp_tendsto (UX_tendsto hd11)).exists_pos
  have hRem : ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)),
      ‖gibbsRem3 (UX (s := s) hd11 x)‖ ≤ C * ‖UX (s := s) hd11 x‖ ^ 3 := by
    filter_upwards [hC0.2.bound] with x hx
    have hx' := hx
    simp only [Function.comp_apply] at hx'
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)] at hx'
    exact hx'
  -- small quantities
  have ht : Tendsto (fun x : ℝ × Coordinates d => |x.1 - 1|) (𝓝 (1, 0)) (𝓝 0) := by
    have := ((continuous_fst.sub continuous_const).abs : Continuous fun x : ℝ × Coordinates d =>
      |x.1 - 1|).tendsto ((1 : ℝ), (0 : Coordinates d))
    simpa using this
  have ha : Tendsto (fun x : ℝ × Coordinates d => ‖Hs.assemblyH d s x.2‖) (𝓝 (1, 0)) (𝓝 0) := by
    have := ((Hs.assemblyH d s).continuous.comp continuous_snd).norm.tendsto
      ((1 : ℝ), (0 : Coordinates d))
    simpa using this
  have hb : Tendsto (fun x : ℝ × Coordinates d => ‖graph (s := s) hd11 x‖) (𝓝 (1, 0)) (𝓝 0) := by
    simpa using (graph_tendsto_zero (s := s) hd11).norm
  have hτ2 : ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)), |x.1| ≤ 2 := by
    have : Tendsto (fun x : ℝ × Coordinates d => |x.1|) (𝓝 (1, 0)) (𝓝 1) := by
      have := ((continuous_fst.abs : Continuous fun x : ℝ × Coordinates d => |x.1|).tendsto
        ((1 : ℝ), (0 : Coordinates d)))
      simpa using this
    filter_upwards [this.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))] with x hx
    exact le_of_lt hx
  have hK0 : 0 ≤ K := by rw [hK]; exact ContinuousLinearMap.opNorm_nonneg _
  have hLn0 : 0 ≤ Ln := by rw [hLn]; exact ContinuousLinearMap.opNorm_nonneg _
  have hLc0 : 0 ≤ Lc := by rw [hLc]; exact ContinuousLinearMap.opNorm_nonneg _
  have hC0' : 0 ≤ C := hC0.1.le
  have hη : ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)),
      K * |x.1 - 1| * Ln + 2 * K * Lc * (‖Hs.assemblyH d s x.2‖ +
        (1 / 2 + 4 * C) * ‖graph (s := s) hd11 x‖) ≤ 1 / 2 := by
    have hlim : Tendsto (fun x : ℝ × Coordinates d => K * |x.1 - 1| * Ln + 2 * K * Lc *
        (‖Hs.assemblyH d s x.2‖ + (1 / 2 + 4 * C) * ‖graph (s := s) hd11 x‖))
        (𝓝 (1, 0)) (𝓝 (K * 0 * Ln + 2 * K * Lc * (0 + (1 / 2 + 4 * C) * 0))) :=
      ((ht.const_mul K).mul_const Ln).add
        ((ha.add (hb.const_mul (1 / 2 + 4 * C))).const_mul (2 * K * Lc))
    simp only [mul_zero, zero_mul, add_zero] at hlim
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx
    exact le_of_lt hx
  have ha1 : ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)), ‖Hs.assemblyH d s x.2‖ ≤ 1 := by
    filter_upwards [ha.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact le_of_lt hx
  have hb1 : ∀ᶠ x in 𝓝 ((1 : ℝ), (0 : Coordinates d)), ‖graph (s := s) hd11 x‖ ≤ 1 := by
    filter_upwards [hb.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx
    exact le_of_lt hx
  have hsol := graph_solves (s := s) hd11
  apply IsBigO.of_bound (2 * (2 * K * Lc * (1 / 2 + 4 * C)) * c ^ 2)
  filter_upwards [hRem, hτ2, hη, ha1, hb1, hsol] with x hRx hτx hηx ha1x hb1x hsolx
  have hmain0 := graph_norm_bound (s := s) hd11 x.1 x.2 (graph hd11 x) hsolx
  rw [← hK, ← hLn, ← hLc] at hmain0
  have hUn : ‖UX (s := s) hd11 x‖ ≤ ‖Hs.assemblyH d s x.2‖ + ‖graph (s := s) hd11 x‖ :=
    norm_add_le _ _
  have hR : ‖gibbsRem3 (Hs.assemblyH d s x.2 + ((graph (s := s) hd11 x : HsC d s) : Hs d s))‖ ≤
      C * (‖Hs.assemblyH d s x.2‖ + ‖graph (s := s) hd11 x‖) ^ 3 := by
    refine hRx.trans (mul_le_mul_of_nonneg_left ?_ hC0')
    exact pow_le_pow_left₀ (norm_nonneg _) hUn 3
  have hfin := absorb_real hK0 hLn0 hLc0 hC0' (norm_nonneg _) (norm_nonneg _) (abs_nonneg _) hτx
    (norm_nonneg _) hR ha1x hb1x hηx hmain0
  have hac : ‖Hs.assemblyH d s x.2‖ ≤ c * ‖x.2‖ := by
    rw [hc]; exact assemblyH_norm_le x.2
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
  calc ‖graph (s := s) hd11 x‖ ≤ 2 * (2 * K * Lc * (1 / 2 + 4 * C)) * ‖Hs.assemblyH d s x.2‖ ^ 2 := hfin
    _ ≤ 2 * (2 * K * Lc * (1 / 2 + 4 * C)) * (c * ‖x.2‖) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hac 2
    _ = _ := by ring

end BecknerOnofri.V2.Reaudit.SobolevQuartic
