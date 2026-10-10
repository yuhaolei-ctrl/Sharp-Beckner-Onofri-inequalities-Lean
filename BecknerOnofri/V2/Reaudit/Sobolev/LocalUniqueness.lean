module

public import BecknerOnofri.V2.Reaudit.Sobolev.GibbsMap
public import BecknerOnofri.RawEulerConvolution
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-! # Stage B: local uniqueness near the base parameter in `H^{11}` (`lem:section4-local-uniqueness`)

Manuscript (Section 4, `lem:section4-local-uniqueness`).  *Let `0 < β₀ < β_s`.  There are an open
interval `J ∋ β₀` and a neighborhood `U` of zero in `H^{11}_0(𝕋^{11})` such that, for every
`β ∈ J`, the only `u ∈ U` satisfying `u = β g * (e^u/∫e^u - 1)` is `u = 0`.*

The proof printed in the manuscript is followed literally:

1. `H^{11}(𝕋^{11})` is a Banach algebra (`s = 11 > 11/2`), so the Euler map
   `F(β, u) = u - β g * (e^u/∫e^u - 1)` is analytic on `ℝ × H^{11}` with values in `H^{11}`
   (`Hs.eulerMap_analytic`, Stage A; `β g * = (β/β_s) T` with `T` the Fourier multiplier
   `1/|k|^{11}` off the mean);
2. its Fréchet derivative in `u` at `(β₀, 0)` is `Id - β₀ T`
   (`Hs.hasFDerivAt_eulerMap_zero`);
3. `Id - β₀ T` is a Fourier multiplier of symbol `1 - β₀/(β_s |k|^{11}) ≥ 1 - β₀/β_s`, so by
   Plancherel it is invertible with `‖(Id - β₀ T)^{-1}‖ ≤ (1 - β₀/β_s)^{-1}`
   (`Hs.resolventEquiv`, `Hs.norm_inverseH_le`);
4. the Banach-space implicit-function theorem (`ContDiffAt.implicitFunction`, analytic version)
   gives, for each `β` near `β₀`, a unique solution of `F(β, u) = 0` near `u = 0`; since
   `F(β, 0) = 0`, that solution is `u = 0`.

Route note.  The implicit-function theorem is applied on the whole Banach algebra `H^{11}`
(not on its closed subspace `H^{11}_0` of mean-zero functions): this is needed to have the
algebra structure (the constant function `1` lies in `H^{11}` but not in `H^{11}_0`) and the
linearization is invertible on all of `H^{11}` (its symbol at `k = 0` is `1`).  The uniqueness
neighborhood in `H^{11}` is then intersected with `H^{11}_0`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## The mean-zero subspace `H^s_0` -/

/-- `H^s_0(𝕋^d)`: the closed subspace of mean-zero elements of `H^s`. -/
def Hs0 (d : ℕ) (s : ℝ) [SobolevIndex d s] : Submodule ℝ (Hs d s) :=
  LinearMap.ker (Hs.meanCLM d s).toLinearMap

theorem Hs0.isClosed : IsClosed (Hs0 d s : Set (Hs d s)) :=
  (Hs.meanCLM d s).isClosed_ker

instance : CompleteSpace (Hs0 d s) := Hs0.isClosed.completeSpace_coe

theorem Hs0.mem_iff (u : Hs d s) : u ∈ Hs0 d s ↔ Hs.meanCLM d s u = 0 := Iff.rfl

/-! ## The linearization `Id - β₀ T` on `H^s_0` and its inverse bound -/

/-- The multiplier `T = g *` of the manuscript on `H^s`: the Fourier multiplier with symbol
`ĝ(k) = 1/(β_s |k|^d)` for `k ≠ 0` and `0` for `k = 0` (`eq:section4-T-multipliers`). -/
def Hs.gMul (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] Hs d s :=
  (spectralThreshold d)⁻¹ • Hs.greenH d s

theorem Hs.coeff_gMul (u : Hs d s) (k : Frequency d) :
    coefficient k (Hs.gMul d s u).val =
      ((if k = 0 then 0 else 1 / (spectralThreshold d * frequencyLength k ^ d) : ℝ) : ℂ) *
        coefficient k u.val := by
  have h := Hs.coeff_greenH u k
  have e : (Hs.gMul d s u).val = (spectralThreshold d)⁻¹ • (Hs.greenH d s u).val := rfl
  rw [e, map_smul, h, Complex.real_smul]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    push_cast
    ring

/-- `β₀ T` is the multiplier `(β₀/β_s) greenH`, so `Id - β₀ T = Hs.forward (β₀/β_s)`. -/
theorem Hs.forward_eq (β₀ : ℝ) :
    Hs.forward d s (β₀ / spectralThreshold d) =
      ContinuousLinearMap.id ℝ (Hs d s) - β₀ • Hs.gMul d s := by
  ext u : 1
  apply Hs.ext
  simp only [Hs.forward, Hs.gMul, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, Hs.val_sub, div_eq_inv_mul, mul_smul, Hs.val_smul, Hs.greenH_val]
  rw [smul_comm]

theorem Hs.mean_inverseH {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) :
    Hs.meanCLM d s (Hs.inverseH d s hμ hμ1 u) = Hs.meanCLM d s u := by
  have h := Hs.coeff_inverseH hμ hμ1 u 0
  have hs0 : SubspectralResolvent.symbol μ (0 : Frequency d) = 1 := by simp [SubspectralResolvent.symbol]
  rw [hs0] at h
  rw [coefficient_zero, coefficient_zero] at h
  simp only [inv_one, Complex.ofReal_one, one_mul] at h
  exact_mod_cast h

/-- The inverse of the linearization `Id - μ T` on the mean-zero space `H^s_0`. -/
def Hs0.inverseH (d : ℕ) (s : ℝ) [SobolevIndex d s] {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    Hs0 d s →L[ℝ] Hs0 d s :=
  (Hs.inverseH d s hμ hμ1).restrict (fun u hu => by
    rw [Hs0.mem_iff] at hu ⊢
    rw [Hs.mean_inverseH]; exact hu)

/-- **`eq:section4-inverse-linearized-bound`** on `H^s_0 → H^s_0`:
`‖(Id - β₀ T)^{-1}‖ ≤ (1 - β₀/β_s)^{-1}`, where `(Id - β₀ T)^{-1}` is the explicit inverse
multiplier (symbol `(1 - β₀/(β_s|k|^d))^{-1}`). -/
theorem Hs0.norm_inverseH_le {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    ‖Hs0.inverseH d s hμ hμ1‖ ≤ (1 - μ)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (sub_pos.mpr hμ1).le) fun u =>
    calc ‖Hs0.inverseH d s hμ hμ1 u‖ = ‖Hs.inverseH d s hμ hμ1 (u : Hs d s)‖ := rfl
      _ ≤ ‖Hs.inverseH d s hμ hμ1‖ * ‖(u : Hs d s)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 - μ)⁻¹ * ‖u‖ := by
          gcongr
          · exact Hs.norm_inverseH_le hμ hμ1
          · exact le_of_eq rfl

/-! ## Local uniqueness for the Euler map on the Banach algebra -/

/-- Banach-space implicit-function theorem for the Euler map `F(μ, u) = u - μ T(e^u/∫e^u - 1)` at
`(μ₀, 0)`, `0 ≤ μ₀ < 1`: near `(μ₀, 0)` the only zeros of `F` have `u = 0`. -/
theorem eulerMap_local_unique {μ₀ : ℝ} (hμ : 0 ≤ μ₀) (hμ1 : μ₀ < 1) :
    ∀ᶠ x : ℝ × Hs d s in 𝓝 (μ₀, 0), Hs.eulerMap x.1 x.2 = 0 → x.2 = 0 := by
  let F := fun x : ℝ × Hs d s => Hs.eulerMap x.1 x.2
  let e := Hs.resolventEquiv d s hμ hμ1
  have hf0 : F (μ₀, 0) = 0 := by simp [F]
  have hfd := Hs.hasFDerivAt_eulerMap_zero (d := d) (s := s) μ₀
  have hpartial : (fderiv ℝ F (μ₀, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (Hs d s)) =
      (e : Hs d s →L[ℝ] Hs d s) := by
    rw [hfd.fderiv]
    ext u
    rfl
  have hinv : ((fderiv ℝ F (μ₀, 0)).comp (ContinuousLinearMap.inr ℝ ℝ (Hs d s))).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.isInvertible_equiv
  have hc : ContDiffAt ℝ ω F (μ₀, 0) := (Hs.eulerMap_analytic μ₀ 0).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  let ψ := hc.implicitFunction hn hinv
  have huniq : ∀ᶠ x in 𝓝 (μ₀, (0 : Hs d s)), F x = 0 ↔ ψ x.1 = x.2 := by
    simpa only [hf0] using hc.eventually_apply_eq_iff_implicitFunction hn hinv
  have hz : ∀ᶠ μ in 𝓝 μ₀, ψ μ = 0 := by
    have ht : Tendsto (fun μ : ℝ => (μ, (0 : Hs d s))) (𝓝 μ₀) (𝓝 (μ₀, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [ht.eventually huniq] with μ hμ
    exact hμ.mp (by simp [F])
  filter_upwards [huniq, (continuous_fst.tendsto (μ₀, (0 : Hs d s))).eventually hz] with x hx hz
  intro hf
  exact (hx.mp hf).symm.trans hz

/-! ## The Euler equation in the manuscript's form -/

/-- The Euler equation `u = β g * (e^u/∫e^u - 1)` of `eq:section4-local-Euler-map-equation`
(equality in `L²`, i.e. almost everywhere), with `g` the Green kernel `realGreen`. -/
def EulerEq (d : ℕ) (β : ℝ) (u : Torus d → ℝ) : Prop :=
  u =ᵐ[torusMeasure d] fun x => β * ∫ y,
    Legacy.TorusEndpoint.GreenKernelReal.realGreen d y * (normalizedGibbs u (x - y) - 1)
      ∂torusMeasure d

theorem Hs.eulerMap_eq_zero_of_eulerEq {β : ℝ} (u : Hs d s) (h : EulerEq d β u.val) :
    Hs.eulerMap (β / spectralThreshold d) u = 0 := by
  have hd := SobolevIndex.hd d s
  have hEq : (u.val : Torus d → ℝ) =ᵐ[torusMeasure d]
      (fun x => ((β / spectralThreshold d) • greenContinuous d (normalized u.val - 1)) x) := by
    filter_upwards [h] with x hx
    rw [hx, RawSubspectralLocalUniqueness.continuous_physical_green hd]
  have : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  have hvEq : u.val = (β / spectralThreshold d) • greenContinuous d (normalized u.val - 1) :=
    ContinuousMap.coe_injective (Measure.eq_of_ae_eq hEq u.val.continuous
      (((β / spectralThreshold d) • greenContinuous d (normalized u.val - 1))).continuous)
  apply Hs.ext
  rw [Hs.val_eulerMap, ← hvEq, sub_self]
  rfl

theorem Hs.eulerEq_of_eulerMap_eq_zero {β : ℝ} (u : Hs d s)
    (h : Hs.eulerMap (β / spectralThreshold d) u = 0) : EulerEq d β u.val := by
  have hd := SobolevIndex.hd d s
  have h0 := congrArg Hs.val h
  rw [Hs.val_eulerMap] at h0
  have h1 : u.val = (β / spectralThreshold d) • greenContinuous d (normalized u.val - 1) :=
    sub_eq_zero.mp h0
  refine Filter.Eventually.of_forall fun x => ?_
  show u.val x = β * ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d y *
    (normalizedGibbs (fun z => u.val z) (x - y) - 1) ∂torusMeasure d
  rw [← RawSubspectralLocalUniqueness.continuous_physical_green hd β u.val x]
  exact congrArg (fun f : Space d => f x) h1

/-! ## Lemma `lem:section4-local-uniqueness` -/

/-- **Local uniqueness near the base parameter in `H^s_0`, `s > d/2`** (Banach-space form, for any
admissible `(d, s)`): for `0 < β₀ < β_s(d)` there are an open interval `J = (a, b) ∋ β₀` and a
neighborhood `U` of `0` in the Banach space `H^s_0(𝕋^d)` such that for `β ∈ J` the only `u ∈ U`
with `u = β g * (e^u/∫e^u - 1)` is `u = 0`. -/
theorem local_uniqueness_Hs {β₀ : ℝ} (h0 : 0 < β₀) (hs : β₀ < spectralThreshold d) :
    ∃ a b : ℝ, a < β₀ ∧ β₀ < b ∧ ∃ U : Set (Hs0 d s), U ∈ 𝓝 (0 : Hs0 d s) ∧
      ∀ β ∈ Set.Ioo a b, ∀ u ∈ U, EulerEq d β (u : Hs d s).val → u = 0 := by
  have hσ := spectralThreshold_pos (SobolevIndex.hd d s)
  have hμ0 : 0 ≤ β₀ / spectralThreshold d := (div_pos h0 hσ).le
  have hμ1 : β₀ / spectralThreshold d < 1 := (div_lt_one hσ).mpr hs
  have hlocal := eulerMap_local_unique (d := d) (s := s) hμ0 hμ1
  have hc : Tendsto (fun x : ℝ × Hs d s => (x.1 / spectralThreshold d, x.2))
      (𝓝 (β₀, 0)) (𝓝 (β₀ / spectralThreshold d, 0)) :=
    ((continuous_fst.div_const (spectralThreshold d)).prodMk continuous_snd).tendsto (β₀, (0 : Hs d s))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hc.eventually hlocal)
  refine ⟨β₀ - δ, β₀ + δ, by linarith, by linarith,
    Metric.ball (0 : Hs0 d s) δ, Metric.ball_mem_nhds _ hδ, fun β hβ u hu hE => ?_⟩
  have hnorm : ‖(u : Hs d s)‖ < δ := by
    have h := hu
    rw [Metric.mem_ball, dist_zero_right] at h
    exact h
  have hdist : dist ((β, (u : Hs d s)) : ℝ × Hs d s) (β₀, 0) < δ := by
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨?_, by simpa only [dist_zero_right] using hnorm⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hβ.1, hβ.2]
  have hzero := hball hdist (Hs.eulerMap_eq_zero_of_eulerEq (u : Hs d s) hE)
  exact Subtype.ext hzero

/-- **Lemma `lem:section4-local-uniqueness`** (`d = 11`, `H^{11}_0(𝕋^{11})`): for `0 < β₀ < β_s`
there are an open interval `J = (a, b) ∋ β₀` and a neighborhood `U` of zero in the Banach space
`H^{11}_0(𝕋^{11})` such that, for every `β ∈ J`, the only `u ∈ U` satisfying
`u = β g * (e^u/∫e^u - 1)` (`g = realGreen 11`, symbol `1/(β_s |k|^{11})`) is `u = 0`. -/
theorem local_uniqueness_H11 {β₀ : ℝ} (h0 : 0 < β₀) (hs : β₀ < spectralThreshold 11) :
    ∃ a b : ℝ, a < β₀ ∧ β₀ < b ∧ ∃ U : Set (Hs0 11 11), U ∈ 𝓝 (0 : Hs0 11 11) ∧
      ∀ β ∈ Set.Ioo a b, ∀ u ∈ U, EulerEq 11 β (u : Hs 11 11).val → u = 0 :=
  local_uniqueness_Hs h0 hs

/-! ## The same statement for raw functions (vocabulary of `V2.Eleven.local_uniqueness`) -/

/-- `lem:section4-local-uniqueness` in the raw vocabulary of `Statement.lean` (and with the same
signature as the continuous-function wrapper `V2.Eleven.local_uniqueness`): `J = (β₀-ε, β₀+ε)` and
`U = {u ∈ H^{11}_0 : ‖u‖_{H^{11}} < ε}`.  Here the proof goes through the Sobolev implicit function
theorem `local_uniqueness_Hs`, not through the continuous-function statement. -/
theorem local_uniqueness_raw {β₀ : ℝ} (h0 : 0 < β₀) (hs : β₀ < spectralThreshold 11) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (β : ℝ) (u : Torus 11 → ℝ), |β - β₀| < ε → InSobolev 11 u → MeanZero u →
      sobolevNorm 11 u < ε → EulerEq 11 β u → u =ᵐ[torusMeasure 11] fun _ => 0 := by
  obtain ⟨a, b, ha, hb, U, hU, hUniq⟩ := local_uniqueness_Hs (d := 11) (s := 11) h0 hs
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  set C := BecknerOnofri.V2.Onset.sobolevAlgConst 11 11 with hC
  have hCpos : 0 < C := algConst_pos 11 11
  refine ⟨min (min (β₀ - a) (b - β₀)) (r / C), lt_min (lt_min (by linarith) (by linarith))
    (div_pos hr hCpos), fun β u hβ hu hm hn hE => ?_⟩
  have hε1 : min (min (β₀ - a) (b - β₀)) (r / C) ≤ min (β₀ - a) (b - β₀) := min_le_left _ _
  have hε2 : min (min (β₀ - a) (b - β₀)) (r / C) ≤ r / C := min_le_right _ _
  obtain ⟨v, hvu, hv, -⟩ := SobolevEmbedding.exists_continuous_representative
    (SobolevIndex.hd 11 11) (SobolevIndex.hs 11 11) u hu
  let w : Hs 11 11 := Hs.mk v hv
  have hmv : MeanZero v := (integral_congr_ae hvu).trans hm
  have hw0 : w ∈ Hs0 11 11 := by
    rw [Hs0.mem_iff, Hs.meanCLM_apply]
    exact hmv
  have hnw : ‖w‖ < r := by
    rw [Hs.norm_eq]
    have h1 : sobolevNorm 11 ⇑w.val = sobolevNorm 11 u := OnsetRaw.sobolevNorm_congr_ae hvu 11
    rw [h1]
    calc C * sobolevNorm 11 u < C * (r / C) := by
          apply mul_lt_mul_of_pos_left _ hCpos
          exact lt_of_lt_of_le hn hε2
      _ = r := by field_simp
  have hwU : (⟨w, hw0⟩ : Hs0 11 11) ∈ U := hrU (by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnw)
  have hm1 : min (β₀ - a) (b - β₀) ≤ β₀ - a := min_le_left _ _
  have hm2 : min (β₀ - a) (b - β₀) ≤ b - β₀ := min_le_right _ _
  have hβJ : β ∈ Set.Ioo a b := by
    rw [abs_lt] at hβ
    constructor <;> linarith [hβ.1, hβ.2]
  have hEv : EulerEq 11 β w.val := by
    refine (hvu.trans hE).mono fun x hx => ?_
    show v x = _
    rw [hx]
    exact congrArg (fun z => β * z) (RawSubspectralLocalUniqueness.green_convolution_congr hvu.symm x)
  have hz := hUniq β hβJ ⟨w, hw0⟩ hwU hEv
  have hw : w = 0 := congrArg Subtype.val hz
  have hv0 : v = 0 := congrArg Hs.val hw
  filter_upwards [hvu] with x hx
  rw [← hx, hv0]
  rfl

end BecknerOnofri.V2.Reaudit.Sobolev
