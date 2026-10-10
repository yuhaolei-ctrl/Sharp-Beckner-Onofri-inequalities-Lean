module

public import BecknerOnofri.V2.Reaudit.Sobolev.Space
public import BecknerOnofri.ReducedEquation
public import BecknerOnofri.GreenPairing

@[expose] public section

/-! # Stage A: the analytic Gibbs map on the Sobolev Banach algebra `H^s(𝕋^d)`, `s > d/2`

This module formalizes the first sentence of the proof of `lem:section4-local-uniqueness` and of
the Lyapunov--Schmidt setup of Section 5: "`H^s(𝕋^d)`, `s > d/2`, is a Banach algebra.
Consequently the map `(β, u) ↦ u - β γ * (e^u / ∫ e^u - 1)` is smooth (analytic) from a
neighborhood of `(β₀, 0)` in `ℝ × H^s` to `H^s`, with Fréchet derivative in `u` at `(β₀, 0)` equal
to `Id - β₀ T`", together with the explicit inverse `(Id - β₀ T)^{-1}` and its norm bound.

All objects live on the Banach algebra `Hs d s` of `Space.lean`:

* `Hs.gibbs : Hs d s → Hs d s`, `u ↦ e^u / ∫ e^u` (normalized Gibbs density), built from Mathlib's
  `NormedSpace.exp` on the complete normed algebra `Hs d s`, with `Hs.gibbs_analytic`
  (`AnalyticAt ℝ` at every point), `Hs.hasFDerivAt_gibbs_zero` (derivative `u ↦ u - ∫u` at `0`),
  `Hs.val_gibbs` (it is the pointwise normalized Gibbs density);
* `Hs.greenH : Hs d s →L[ℝ] Hs d s`, the Fourier multiplier `1/|k|^d` (`k ≠ 0`), `0` (`k = 0`),
  i.e. `T = g *` of the manuscript up to the factor `β_s` (so `β g * = (β/β_s) greenH`);
* `Hs.eulerMap μ u = u - μ greenH (gibbs u - 1)`, jointly analytic in `(μ, u)`, with
  `Hs.hasFDerivAt_eulerMap_zero`: the partial derivative in `u` at `(μ, 0)` is `Id - μ greenH`;
* `Hs.resolventEquiv`, the continuous linear equivalence `Id - μ greenH` of `H^s` for `0 ≤ μ < 1`
  with explicit inverse multiplier of symbol `(1 - μ/|k|^d)^{-1}`, and the Plancherel bound
  `Hs.norm_inverse_le : ‖(Id - μ greenH)^{-1}‖ ≤ (1 - μ)^{-1}`
  (`eq:section4-inverse-linearized-bound` with `μ = β₀/β_s`). -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## Fourier multipliers acting on `H^s` -/

theorem Hs.norm_encodeAlg_apply (u : Hs d s) (k : Frequency d) :
    ‖Hs.encodeAlg d s u k‖ =
      BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevScale s k * ‖coefficient k u.val‖ := by
  have hC := (algConst_pos d s).le
  have hw := (sobolevScale_pos s k).le
  simp only [Hs.encodeAlg, LinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, Hs.encode_apply,
    scaledCoeff, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
    abs_of_nonneg hw]
  ring

/-- Plancherel comparison: a coefficientwise bound on `H^s` functions gives a norm bound. -/
theorem Hs.norm_le_of_coeff_le {u v : Hs d s} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k, ‖coefficient k v.val‖ ≤ M * ‖coefficient k u.val‖) : ‖v‖ ≤ M * ‖u‖ := by
  have hle : ‖Hs.encodeAlg d s v‖ ≤ ‖M • Hs.encodeAlg d s u‖ := by
    apply lp.norm_mono (by norm_num)
    intro k
    rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hM, Hs.norm_encodeAlg_apply,
      Hs.norm_encodeAlg_apply]
    have hC := (algConst_pos d s).le
    have hw := (sobolevScale_pos s k).le
    calc _ ≤ BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevScale s k *
          (M * ‖coefficient k u.val‖) := by gcongr; exact h k
      _ = _ := by ring
  calc ‖v‖ = ‖Hs.encodeAlg d s v‖ := rfl
    _ ≤ ‖M • Hs.encodeAlg d s u‖ := hle
    _ = M * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hM]; rfl

omit [SobolevIndex d s] in
theorem inSobolev_of_coeff_le {u v : Space d} (hu : InSobolev s ⇑u) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k, ‖coefficient k v‖ ≤ M * ‖coefficient k u‖) : InSobolev s ⇑v := by
  rw [inSobolev_iff_memℓp] at hu ⊢
  refine (hu.const_smul M).mono' fun k => ?_
  simp only [scaledCoeff, Pi.smul_apply, norm_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sobolevScale_pos s k).le, abs_of_nonneg hM]
  calc sobolevScale s k * ‖coefficient k v‖
      ≤ sobolevScale s k * (M * ‖coefficient k u‖) :=
        mul_le_mul_of_nonneg_left (h k) (sobolevScale_pos s k).le
    _ = M * (sobolevScale s k * ‖coefficient k u‖) := by ring

/-- Restriction of a continuous operator on `C(𝕋^d, ℝ)` that acts on Fourier coefficients by
multipliers bounded by `M` to an operator on `H^s`, of norm at most `M`. -/
def Hs.restrictCLM (L : Space d →L[ℝ] Space d) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (u : Space d) (k : Frequency d), ‖coefficient k (L u)‖ ≤ M * ‖coefficient k u‖) :
    Hs d s →L[ℝ] Hs d s :=
  LinearMap.mkContinuous
    { toFun := fun u => Hs.mk (L u.val) (inSobolev_of_coeff_le u.inSobolev hM (h u.val))
      map_add' := fun u v => Hs.ext (by simp)
      map_smul' := fun c u => Hs.ext (by simp) }
    M (fun u => Hs.norm_le_of_coeff_le hM (fun k => h u.val k))

@[simp] theorem Hs.restrictCLM_val (L : Space d →L[ℝ] Space d) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (u : Space d) (k : Frequency d), ‖coefficient k (L u)‖ ≤ M * ‖coefficient k u‖)
    (u : Hs d s) : (Hs.restrictCLM L M hM h u).val = L u.val := rfl

theorem Hs.norm_restrictCLM_le (L : Space d →L[ℝ] Space d) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ (u : Space d) (k : Frequency d), ‖coefficient k (L u)‖ ≤ M * ‖coefficient k u‖) :
    ‖(Hs.restrictCLM L M hM h : Hs d s →L[ℝ] Hs d s)‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM fun u =>
    Hs.norm_le_of_coeff_le hM (fun k => h u.val k)

/-! ## The Green multiplier `T` -/

theorem green_coeff_norm_le (hd : 0 < d) (u : Space d) (k : Frequency d) :
    ‖coefficient k (greenContinuous d u)‖ ≤ 1 * ‖coefficient k u‖ := by
  rw [coefficient_green hd, norm_mul, Complex.norm_real]
  by_cases hk : k = 0
  · simp [hk]
  · have h1 := GreenCritical.nonzero_eigenvalue_ge_one (⟨k, hk⟩ : NonzeroFrequency d)
    have h2 : (1 : ℝ) / frequencyLength k ^ d ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le zero_lt_one h1)]; exact h1
    have h3 : 0 ≤ (1 : ℝ) / frequencyLength k ^ d := by
      have := lt_of_lt_of_le zero_lt_one h1
      positivity
    simp only [hk, ite_false, Real.norm_eq_abs, abs_of_nonneg h3]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- The Fourier multiplier `1/|k|^d` (`k ≠ 0`), `0` (`k = 0`) on `H^s`: the operator `T = g *` of
`eq:section4-T-multipliers` up to the factor `1/β_s`
(`g` has symbol `1/(β_s |k|^d)`), equivalently `(2π)^d (-Δ)^{-d/2}` on mean-zero functions. -/
def Hs.greenH (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] Hs d s :=
  Hs.restrictCLM (greenContinuous d) 1 zero_le_one (green_coeff_norm_le (SobolevIndex.hd d s))

@[simp] theorem Hs.greenH_val (u : Hs d s) : (Hs.greenH d s u).val = greenContinuous d u.val := rfl

theorem Hs.coeff_greenH (u : Hs d s) (k : Frequency d) :
    coefficient k (Hs.greenH d s u).val =
      ((if k = 0 then 0 else 1 / frequencyLength k ^ d : ℝ) : ℂ) * coefficient k u.val :=
  coefficient_green (SobolevIndex.hd d s) u.val k

theorem Hs.norm_greenH_le : ‖Hs.greenH d s‖ ≤ 1 :=
  Hs.norm_restrictCLM_le _ _ _ _

theorem Hs.meanCLM_greenH (u : Hs d s) : Hs.meanCLM d s (Hs.greenH d s u) = 0 := by
  have := ReducedEquation.mean_green (SobolevIndex.hd d s) u.val
  simpa using this

@[simp] theorem Hs.greenH_one : Hs.greenH d s 1 = 0 := by
  apply Hs.ext
  simp only [Hs.greenH_val, Hs.val_one, Hs.val_zero]
  exact BecknerOnofri.HighDim.GreenPairing.green_one (SobolevIndex.hd d s)

/-! ## The exponential and the normalized Gibbs map on `H^s` -/

/-- The `ℚ`-normed algebra structure used by Mathlib's `NormedSpace.exp` API (obtained from the real
one by restriction of scalars, as for every real normed algebra). -/
instance : NormedAlgebra ℚ (Hs d s) := NormedAlgebra.restrictScalars ℚ ℝ (Hs d s)

/-- The exponential `e^u` in the Banach algebra `H^s` (Mathlib's `NormedSpace.exp`) is the
pointwise exponential of the continuous representative. -/
theorem Hs.val_exp (u : Hs d s) : (NormedSpace.exp u).val = exponential u.val :=
  NormedSpace.map_exp (Hs.toSpaceAlg (d := d) (s := s)) (Hs.toSpaceCLM d s).continuous u

theorem Hs.exp_apply (u : Hs d s) (x : Torus d) :
    (NormedSpace.exp u).val x = Real.exp (u.val x) := by
  rw [Hs.val_exp, exponential_apply]

/-- The partition function `Z(u) = ∫ e^u dm_d` on `H^s`. -/
def Hs.partition (u : Hs d s) : ℝ := Hs.meanCLM d s (NormedSpace.exp u)

theorem Hs.partition_eq (u : Hs d s) : Hs.partition u = ContinuousGibbs.partition u.val := by
  simp [Hs.partition, ContinuousGibbs.partition, Hs.val_exp]

theorem Hs.partition_pos (u : Hs d s) : 0 < Hs.partition u := by
  rw [Hs.partition_eq]; exact ContinuousGibbs.partition_pos _

/-- The normalized Gibbs density `e^u / ∫ e^u` as a map `H^s → H^s`. -/
def Hs.gibbs (u : Hs d s) : Hs d s := (Hs.partition u)⁻¹ • NormedSpace.exp u

theorem Hs.val_gibbs (u : Hs d s) : (Hs.gibbs u).val = normalized u.val := by
  rw [Hs.gibbs, Hs.val_smul, Hs.val_exp, Hs.partition_eq]
  rfl

theorem Hs.gibbs_apply (u : Hs d s) (x : Torus d) :
    (Hs.gibbs u).val x = normalizedGibbs (fun y => u.val y) x := by
  rw [Hs.val_gibbs, normalized_apply]

theorem Hs.meanCLM_gibbs (u : Hs d s) : Hs.meanCLM d s (Hs.gibbs u) = 1 := by
  rw [Hs.meanCLM_apply, Hs.val_gibbs, mean_normalized]

@[simp] theorem Hs.partition_zero : Hs.partition (0 : Hs d s) = 1 := by
  rw [Hs.partition_eq]; simp

@[simp] theorem Hs.gibbs_zero : Hs.gibbs (0 : Hs d s) = 1 := by
  apply Hs.ext
  rw [Hs.val_gibbs]; simp

theorem Hs.exp_analytic (u : Hs d s) : AnalyticAt ℝ (NormedSpace.exp : Hs d s → Hs d s) u :=
  NormedSpace.exp_analytic u

theorem Hs.partition_analytic (u : Hs d s) : AnalyticAt ℝ (Hs.partition : Hs d s → ℝ) u :=
  ((Hs.meanCLM d s).analyticAt (NormedSpace.exp u)).comp (Hs.exp_analytic u)

/-- **The Gibbs map is analytic on the Sobolev Banach algebra** (`H^s`, `s > d/2`). -/
theorem Hs.gibbs_analytic (u : Hs d s) : AnalyticAt ℝ (Hs.gibbs : Hs d s → Hs d s) u :=
  ((Hs.partition_analytic u).inv (Hs.partition_pos u).ne').smul (Hs.exp_analytic u)

theorem Hs.gibbs_contDiffAt (u : Hs d s) : ContDiffAt ℝ ω (Hs.gibbs : Hs d s → Hs d s) u :=
  (Hs.gibbs_analytic u).contDiffAt

/-- Centering `u ↦ u - ∫ u` on `H^s`. -/
def Hs.center (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] Hs d s :=
  ContinuousLinearMap.id ℝ (Hs d s) - (Hs.meanCLM d s).smulRight (1 : Hs d s)

@[simp] theorem Hs.center_apply (u : Hs d s) :
    Hs.center d s u = u - (Hs.meanCLM d s u) • (1 : Hs d s) := rfl

theorem Hs.val_center (u : Hs d s) : (Hs.center d s u).val = ContinuousGibbs.center d u.val := by
  ext x
  simp [Hs.center_apply]

theorem Hs.hasFDerivAt_partition_zero :
    HasFDerivAt (Hs.partition : Hs d s → ℝ) (Hs.meanCLM d s) 0 := by
  have he : HasFDerivAt (NormedSpace.exp : Hs d s → Hs d s) (1 : Hs d s →L[ℝ] Hs d s) 0 :=
    hasFDerivAt_exp_zero
  convert! (Hs.meanCLM d s).hasFDerivAt.comp 0 he using 1

/-- **Derivative of the Gibbs map on `H^s` at zero**: `D gibbs(0) u = u - ∫ u`. -/
theorem Hs.hasFDerivAt_gibbs_zero :
    HasFDerivAt (Hs.gibbs : Hs d s → Hs d s) (Hs.center d s) 0 := by
  have he : HasFDerivAt (NormedSpace.exp : Hs d s → Hs d s) (1 : Hs d s →L[ℝ] Hs d s) 0 :=
    hasFDerivAt_exp_zero
  have hi := (hasDerivAt_inv (by simp : Hs.partition (0 : Hs d s) ≠ 0)).comp_hasFDerivAt
    (0 : Hs d s) Hs.hasFDerivAt_partition_zero
  have h := hi.smul he
  convert! h using 1
  ext f
  simp [Hs.center_apply, sub_eq_add_neg]

/-- The nonlinear remainder of the Gibbs map: `gibbs u - 1 - (u - ∫ u)`. -/
def Hs.gibbsRemainder (u : Hs d s) : Hs d s := Hs.gibbs u - 1 - Hs.center d s u

theorem Hs.gibbsRemainder_analytic (u : Hs d s) : AnalyticAt ℝ (Hs.gibbsRemainder : Hs d s → Hs d s) u :=
  ((Hs.gibbs_analytic u).sub analyticAt_const).sub ((Hs.center d s).analyticAt u)

@[simp] theorem Hs.gibbsRemainder_zero : Hs.gibbsRemainder (0 : Hs d s) = 0 := by
  simp [Hs.gibbsRemainder]

theorem Hs.hasFDerivAt_gibbsRemainder_zero :
    HasFDerivAt (𝕜 := ℝ) (Hs.gibbsRemainder : Hs d s → Hs d s) 0 0 := by
  convert! ((Hs.hasFDerivAt_gibbs_zero (d := d) (s := s)).sub_const (1 : Hs d s)).sub
    ((Hs.center d s).hasFDerivAt (x := (0 : Hs d s))) using 1
  simp

/-- **Quadratic remainder of the Gibbs map in `H^s`**: `gibbs u = 1 + (u - ∫u) + O(‖u‖²)`. -/
theorem Hs.gibbsRemainder_isBigO :
    (Hs.gibbsRemainder : Hs d s → Hs d s) =O[𝓝 (0 : Hs d s)] (fun u => ‖u‖ ^ 2) := by
  obtain ⟨p, hp⟩ := Hs.gibbsRemainder_analytic (0 : Hs d s)
  have h0 (u : Fin 0 → Hs d s) : p 0 u = 0 := by
    simpa using hp.coeff_zero u
  have h1 : continuousMultilinearCurryFin1 ℝ (Hs d s) (Hs d s) (p 1) = 0 :=
    hp.hasFDerivAt.unique Hs.hasFDerivAt_gibbsRemainder_zero
  have h1' (u : Hs d s) : p 1 (fun _ => u) = 0 := by
    have h := congrArg (fun f : Hs d s →L[ℝ] Hs d s => f u) h1
    exact h
  have hsum (u : Hs d s) : p.partialSum 2 u = 0 := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, h0, h1']
  simpa only [zero_add, hsum, sub_zero] using hp.isBigO_sub_partialSum_pow 2

/-! ## The Euler map and its linearization -/

theorem Hs.greenH_center (u : Hs d s) : Hs.greenH d s (Hs.center d s u) = Hs.greenH d s u := by
  rw [Hs.center_apply, map_sub, map_smul, Hs.greenH_one, smul_zero, sub_zero]

/-- The Euler map `𝓕(μ, u) = u - μ T(e^u/∫e^u - 1)` of `eq:section4-implicit-map` on `H^s`,
where `μ = β/β_s` and `β g * = μ · greenH` (the symbol of `g` is `1/(β_s |k|^d)`). -/
def Hs.eulerMap (μ : ℝ) (u : Hs d s) : Hs d s := u - μ • Hs.greenH d s (Hs.gibbs u - 1)

theorem Hs.val_eulerMap (μ : ℝ) (u : Hs d s) :
    (Hs.eulerMap μ u).val = u.val - μ • greenContinuous d (normalized u.val - 1) := by
  simp [Hs.eulerMap, Hs.val_gibbs, BecknerOnofri.HighDim.GreenPairing.green_one (SobolevIndex.hd d s)]

@[simp] theorem Hs.eulerMap_zero (μ : ℝ) : Hs.eulerMap μ (0 : Hs d s) = 0 := by
  apply Hs.ext
  simp [Hs.val_eulerMap]

/-- **The Euler map is analytic** (jointly in the parameter and the Sobolev potential). -/
theorem Hs.eulerMap_analytic (μ : ℝ) (u : Hs d s) :
    AnalyticAt ℝ (fun x : ℝ × Hs d s => Hs.eulerMap x.1 x.2) (μ, u) := by
  have hg : AnalyticAt ℝ (fun x : ℝ × Hs d s => Hs.gibbs x.2) (μ, u) :=
    (Hs.gibbs_analytic u).comp_of_eq ((ContinuousLinearMap.snd ℝ ℝ (Hs d s)).analyticAt (μ, u)) rfl
  have hr : AnalyticAt ℝ (fun x : ℝ × Hs d s => Hs.gibbs x.2 - 1) (μ, u) :=
    hg.sub analyticAt_const
  have hG : AnalyticAt ℝ (fun x : ℝ × Hs d s => Hs.greenH d s (Hs.gibbs x.2 - 1)) (μ, u) :=
    ((Hs.greenH d s).analyticAt _).comp hr
  exact analyticAt_snd.sub (analyticAt_fst.smul hG)

/-- **Fréchet derivative of the Euler map at `(μ, 0)`**: `D𝓕(μ,0)(t, v) = v - μ T v`
(`eq:section4-linearized-Euler-map`). -/
theorem Hs.hasFDerivAt_eulerMap_zero (μ : ℝ) :
    HasFDerivAt (fun x : ℝ × Hs d s => Hs.eulerMap x.1 x.2)
      ((ContinuousLinearMap.id ℝ (Hs d s) - μ • Hs.greenH d s).comp
        (ContinuousLinearMap.snd ℝ ℝ (Hs d s))) (μ, 0) := by
  let P := ContinuousLinearMap.snd ℝ ℝ (Hs d s)
  let Q := ContinuousLinearMap.fst ℝ ℝ (Hs d s)
  have hn := (Hs.hasFDerivAt_gibbs_zero (d := d) (s := s)).comp (μ, (0 : Hs d s)) P.hasFDerivAt
  have hg := (Hs.greenH d s).hasFDerivAt.comp (μ, (0 : Hs d s)) (hn.sub_const 1)
  have hh := (P.hasFDerivAt (x := (μ, (0 : Hs d s)))).sub
    ((Q.hasFDerivAt (x := (μ, (0 : Hs d s)))).smul hg)
  convert! hh using 1
  apply ContinuousLinearMap.ext
  intro y
  simp [P, Q, Hs.greenH_one]

/-! ## The inverse multiplier of the linearization -/

/-- The linearization `Id - μ T` of the Euler map. -/
def Hs.forward (d : ℕ) (s : ℝ) [SobolevIndex d s] (μ : ℝ) : Hs d s →L[ℝ] Hs d s :=
  ContinuousLinearMap.id ℝ (Hs d s) - μ • Hs.greenH d s

theorem Hs.val_forward (μ : ℝ) (u : Hs d s) :
    ((Hs.forward d s μ) u).val = SubspectralResolvent.forward d μ u.val := rfl

theorem Hs.coeff_forward (μ : ℝ) (u : Hs d s) (k : Frequency d) :
    coefficient k ((Hs.forward d s μ) u).val =
      (SubspectralResolvent.symbol μ k : ℂ) * coefficient k u.val :=
  SubspectralResolvent.forward_fourier (SobolevIndex.hd d s) μ u.val k

theorem inverse_coeff_le (hd : 0 < d) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Space d)
    (k : Frequency d) :
    ‖coefficient k (SubspectralResolvent.inverse hμ hμ1 u)‖ ≤ (1 - μ)⁻¹ * ‖coefficient k u‖ := by
  rw [SubspectralResolvent.inverse_fourier hd, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (SubspectralResolvent.symbol_inv_bound hμ hμ1 k) (norm_nonneg _)

/-- The explicit inverse multiplier `(Id - μ T)^{-1}` on `H^s`: the Fourier multiplier with symbol
`(1 - μ/|k|^d)^{-1}` (`k ≠ 0`), `1` (`k = 0`). -/
def Hs.inverseH (d : ℕ) (s : ℝ) [SobolevIndex d s] {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    Hs d s →L[ℝ] Hs d s :=
  Hs.restrictCLM (SubspectralResolvent.inverse hμ hμ1) ((1 - μ)⁻¹)
    (inv_nonneg.mpr (sub_pos.mpr hμ1).le) (inverse_coeff_le (SobolevIndex.hd d s) hμ hμ1)

theorem Hs.coeff_inverseH {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) (k : Frequency d) :
    coefficient k (Hs.inverseH d s hμ hμ1 u).val =
      (((SubspectralResolvent.symbol μ k)⁻¹ : ℝ) : ℂ) * coefficient k u.val :=
  SubspectralResolvent.inverse_fourier (SobolevIndex.hd d s) hμ hμ1 u.val k

/-- **Plancherel bound for the inverse of the linearization**
(`eq:section4-inverse-linearized-bound`, with `μ = β₀/β_s`):
`‖(Id - μ T)^{-1}‖_{H^s → H^s} ≤ (1 - μ)^{-1}`.  (The norm on `Hs d s` is a constant multiple of the
`H^s` norm, so the operator norm is the same as for the `H^s` norm.) -/
theorem Hs.norm_inverseH_le {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    ‖Hs.inverseH d s hμ hμ1‖ ≤ (1 - μ)⁻¹ :=
  Hs.norm_restrictCLM_le _ _ _ _

theorem Hs.inverseH_forward {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) :
    Hs.inverseH d s hμ hμ1 (Hs.forward d s μ u) = u :=
  Hs.ext (SubspectralResolvent.inverse_left (SobolevIndex.hd d s) hμ hμ1 u.val)

theorem Hs.forward_inverseH {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) :
    Hs.forward d s μ (Hs.inverseH d s hμ hμ1 u) = u :=
  Hs.ext (SubspectralResolvent.inverse_right (SobolevIndex.hd d s) hμ hμ1 u.val)

/-- `Id - μ T` is a continuous linear equivalence of `H^s` for `0 ≤ μ < 1`, with the explicit
inverse multiplier `Hs.inverseH`. -/
def Hs.resolventEquiv (d : ℕ) (s : ℝ) [SobolevIndex d s] {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) :
    Hs d s ≃L[ℝ] Hs d s where
  toLinearEquiv :=
    { toFun := Hs.forward d s μ
      invFun := Hs.inverseH d s hμ hμ1
      left_inv := Hs.inverseH_forward hμ hμ1
      right_inv := Hs.forward_inverseH hμ hμ1
      map_add' := map_add _
      map_smul' := map_smul _ }
  continuous_toFun := (Hs.forward d s μ).continuous
  continuous_invFun := (Hs.inverseH d s hμ hμ1).continuous

@[simp] theorem Hs.resolventEquiv_apply {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) :
    Hs.resolventEquiv d s hμ hμ1 u = Hs.forward d s μ u := rfl

@[simp] theorem Hs.resolventEquiv_symm_apply {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (u : Hs d s) :
    (Hs.resolventEquiv d s hμ hμ1).symm u = Hs.inverseH d s hμ hμ1 u := rfl

end BecknerOnofri.V2.Reaudit.Sobolev
