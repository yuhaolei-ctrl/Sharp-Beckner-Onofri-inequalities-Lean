module

public import BecknerOnofri.V2.Reaudit.HeatKernel.ResolventLimit

@[expose] public section

/-! # Strong resolvent convergence and the resolvent comparison for `B_m` (U05/S015, step 4)

Main results (`m ≥ 1`, `μ > 0`, `c = m(m-1)`, `f ≥ 0` in `L²(0,π)`):

* `Rk_tendsto`: `R_k f → (B_m+μ)^{-1} f` for every `f` (`resOp hm μ` is the repository's spectral
  inverse of `B_m + μ`), where `R_k` is the resolvent of `P_D + c + min(c cot², k)`.
* `resOp_nonneg`: `0 ≤ (B_m+μ)^{-1} f`.
* `resOp_le`: `(B_m+μ)^{-1} f ≤ (P_D + μ + c)^{-1} f`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann Legacy.BecknerOnofri.BoundedL2Multiplier

/-! ### Strong convergence from a Hilbert basis and a uniform bound -/

theorem tendsto_of_dense_basis {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (e : HilbertBasis ι ℝ H) {A : ℕ → H →L[ℝ] H} {B : H →L[ℝ] H} {C : ℝ}
    (hC : ∀ k, ‖A k‖ ≤ C)
    (hlim : ∀ i, Tendsto (fun k => A k (e i)) atTop (𝓝 (B (e i)))) (u : H) :
    Tendsto (fun k => A k u) atTop (𝓝 (B u)) := by
  let K : Submodule ℝ H :=
    { carrier := {u | Tendsto (fun k => A k u) atTop (𝓝 (B u))}
      add_mem' := fun {a b} ha hb => by
        have := Tendsto.add (ha : Tendsto (fun k => A k a) atTop (𝓝 (B a)))
          (hb : Tendsto (fun k => A k b) atTop (𝓝 (B b)))
        show Tendsto (fun k => A k (a + b)) atTop (𝓝 (B (a + b)))
        simpa only [map_add] using this
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have := Tendsto.const_smul (hx : Tendsto (fun k => A k x) atTop (𝓝 (B x))) c
        show Tendsto (fun k => A k (c • x)) atTop (𝓝 (B (c • x)))
        simpa only [map_smul] using this }
  have hspan : Submodule.span ℝ (Set.range e) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hlim i
  have hclosed : IsClosed (K : Set H) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq x hseq hx
    change Tendsto (fun k => A k x) atTop (𝓝 (B x))
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨D, hD⟩ : ∃ D, D = C + ‖B‖ + 1 := ⟨_, rfl⟩
    have hDpos : 0 < D := by rw [hD]; linarith [norm_nonneg B]
    obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hx) (ε / (3 * D)) (by positivity)
    have hs := hN0 N0 le_rfl
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hseq N0)) (ε / 3) (by positivity)
    refine ⟨N, fun k hk => ?_⟩
    have h1 := hN k hk
    rw [dist_eq_norm] at hs h1 ⊢
    have e1 : A k x - B x =
        A k (x - seq N0) + (A k (seq N0) - B (seq N0)) + B (seq N0 - x) := by
      simp only [map_sub]; abel
    have hs' : ‖x - seq N0‖ = ‖seq N0 - x‖ := norm_sub_rev _ _
    have hA : ‖A k (x - seq N0)‖ ≤ C * ‖seq N0 - x‖ := by
      rw [← hs']
      exact ((A k).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _))
    have hB : ‖B (seq N0 - x)‖ ≤ ‖B‖ * ‖seq N0 - x‖ := B.le_opNorm _
    have hδ : ‖seq N0 - x‖ * (3 * D) < ε := (lt_div_iff₀ (by positivity)).mp hs
    rw [e1]
    have h3 := norm_add₃_le (a := A k (x - seq N0)) (b := A k (seq N0) - B (seq N0))
      (c := B (seq N0 - x))
    have h4 : (C + ‖B‖) * ‖seq N0 - x‖ ≤ D * ‖seq N0 - x‖ :=
      mul_le_mul_of_nonneg_right (by rw [hD]; linarith) (norm_nonneg _)
    nlinarith [norm_nonneg (seq N0 - x)]
  have hmin := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [e.dense_span] at hmin
  exact hmin (Submodule.mem_top : u ∈ (⊤ : Submodule ℝ H))

/-! ### The convergence of `R_k` on the eigenfunctions -/

section Basis
variable {m : ℕ} (hm : 0 < m)
include hm

theorem Rk_phi {μ : ℝ} (hμ : 0 < μ) (k j : ℕ) :
    Rk (cc m) (cc_nonneg hm) μ k
      ((eigenvalue m j + μ) • normalizedVector m j - omegaL m j +
        Wop (cc m) (cc_nonneg hm) k (normalizedVector m j)) = normalizedVector m j := by
  have hc := cc_nonneg hm
  have h0 : 0 < μ + cc m := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hnk : 0 < μ + cc m + k := by linarith
  have key := key_identity hm hμ j
  have hTn := Tk_norm_lt_one (cc m) hc hμ k
  set φ := normalizedVector m j with hφ
  set a : JacobiL2 := (eigenvalue m j + μ) • φ - omegaL m j with ha
  have e1 : S (μ + cc m + k) a = φ - (k : ℝ) • S (μ + cc m + k) φ := by
    have h1 := S_sub h0 hnk a
    have h2 := S_comm h0 hnk a
    rw [show μ + cc m + (k : ℝ) - (μ + cc m) = k by ring, key] at h1
    rw [key] at h2
    rw [h2] at h1
    calc S (μ + cc m + k) a = φ - (φ - S (μ + cc m + k) a) := by abel
      _ = _ := by rw [h1]
  have e2 : S (μ + cc m + k) (a + Wop (cc m) hc k φ) = φ - Tk (cc m) hc μ k φ := by
    rw [map_add, e1, Tk_apply]
    abel
  change neumannOperator intervalMeasure (Tk (cc m) hc μ k)
    (S (μ + cc m + k) (a + Wop (cc m) hc k φ)) = φ
  rw [e2]
  exact neumann_left_inverse intervalMeasure hTn φ

theorem Rk_basis_eq {μ : ℝ} (hμ : 0 < μ) (k j : ℕ) :
    (eigenvalue m j + μ) • Rk (cc m) (cc_nonneg hm) μ k (normalizedVector m j) -
      Rk (cc m) (cc_nonneg hm) μ k
        (omegaL m j - Wop (cc m) (cc_nonneg hm) k (normalizedVector m j)) =
      normalizedVector m j := by
  have h := Rk_phi hm hμ k j
  have e : (eigenvalue m j + μ) • normalizedVector m j - omegaL m j +
      Wop (cc m) (cc_nonneg hm) k (normalizedVector m j) =
      (eigenvalue m j + μ) • normalizedVector m j -
        (omegaL m j - Wop (cc m) (cc_nonneg hm) k (normalizedVector m j)) := by abel
  rw [e, map_sub, map_smul] at h
  exact h

/-- `ω_j - W_k φ_j → 0` in `L²`: dominated convergence, `|ω_j - W_kφ_j| ≤ |ω_j| ≤ M`. -/
theorem omega_sub_W_tendsto (j : ℕ) :
    Tendsto (fun k : ℕ =>
      ‖omegaL m j - Wop (cc m) (cc_nonneg hm) k (normalizedVector m j)‖) atTop (𝓝 0) := by
  have hc := cc_nonneg hm
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi)).exists_bound_of_continuousOn
    (omegaFn_continuous m j).continuousOn
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, Real.pi_pos.le⟩)
  set g := normalizedFunction m j with hg
  let vf : ℕ → ℝ → ℝ := fun k x => omegaFn m j x - cotTrunc (cc m) k x * g x
  have hvm : ∀ k, Measurable (vf k) := fun k =>
    (omegaFn_continuous m j).measurable.sub
      ((measurable_cotTrunc (cc m) k).mul (normalizedFunction_contDiff m j).continuous.measurable)
  have hv : ∀ k, (⇑(omegaL m j - Wop (cc m) hc k (normalizedVector m j)) : ℝ → ℝ)
      =ᵐ[intervalMeasure] vf k := by
    intro k
    filter_upwards [Lp.coeFn_sub (omegaL m j) (Wop (cc m) hc k (normalizedVector m j)),
      omegaL_ae m j, (wt (cc m) hc k).operator_ae (normalizedVector m j),
      normalizedVector_ae_eq m j] with x h1 h2 h3 h4
    have h3' : Wop (cc m) hc k (normalizedVector m j) x =
        cotTrunc (cc m) k x * normalizedVector m j x := h3
    rw [h1, Pi.sub_apply, h2, h3', h4]
  have hnorm : ∀ k, ‖omegaL m j - Wop (cc m) hc k (normalizedVector m j)‖ ^ 2 =
      ∫ x, vf k x * vf k x ∂intervalMeasure := by
    intro k
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv k] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
  have hlim : Tendsto (fun k : ℕ => ∫ x, vf k x * vf k x ∂intervalMeasure) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := intervalMeasure)
      (F := fun (k : ℕ) x => vf k x * vf k x) (f := fun _ => (0 : ℝ)) (fun _ => M ^ 2)
      (fun k => ((hvm k).mul (hvm k)).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · simpa using this
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hb0 := cotTrunc_nonneg hc k x
      have hb1 := cotTrunc_le_cot2 (cc m) k x
      have hω := omegaFn_eq m j hx
      have hωM := hM x ⟨hx.1.le, hx.2.le⟩
      have e : vf k x = (cot2 (cc m) x - cotTrunc (cc m) k x) * g x := by
        simp only [vf]; rw [hω]; ring
      have hle : |vf k x| ≤ M := by
        rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ cot2 (cc m) x - cotTrunc (cc m) k x)]
        calc (cot2 (cc m) x - cotTrunc (cc m) k x) * |g x| ≤ cot2 (cc m) x * |g x| :=
              mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ = |omegaFn m j x| := by
              rw [hω, abs_mul, abs_of_nonneg (cot2_nonneg hc x)]
          _ ≤ M := hωM
      rw [Real.norm_eq_abs]
      calc |vf k x * vf k x| = |vf k x| * |vf k x| := abs_mul _ _
        _ ≤ M * M := mul_le_mul hle hle (abs_nonneg _) hM0
        _ = M ^ 2 := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      obtain ⟨K, hK⟩ := exists_nat_ge (cot2 (cc m) x)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      have : cotTrunc (cc m) k x = cot2 (cc m) x :=
        min_eq_left (hK.trans (by exact_mod_cast hk))
      have e : vf k x = 0 := by
        simp only [vf]; rw [this, omegaFn_eq m j hx]; ring
      rw [e]; ring
  have h2 : Tendsto (fun k : ℕ =>
      ‖omegaL m j - Wop (cc m) hc k (normalizedVector m j)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hnorm] using hlim
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h3

theorem Rk_basis_tendsto {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    Tendsto (fun k : ℕ => Rk (cc m) (cc_nonneg hm) μ k (normalizedVector m j)) atTop
      (𝓝 ((eigenvalue m j + μ)⁻¹ • normalizedVector m j)) := by
  have hc := cc_nonneg hm
  have hlam : 0 < eigenvalue m j + μ := by linarith [eigenvalue_nonneg' m j]
  have hR : ∀ k : ℕ, Rk (cc m) hc μ k (normalizedVector m j) =
      (eigenvalue m j + μ)⁻¹ • (normalizedVector m j +
        Rk (cc m) hc μ k (omegaL m j - Wop (cc m) hc k (normalizedVector m j))) := by
    intro k
    have h := Rk_basis_eq hm hμ k j
    have h' : (eigenvalue m j + μ) • Rk (cc m) hc μ k (normalizedVector m j) =
        normalizedVector m j + Rk (cc m) hc μ k
          (omegaL m j - Wop (cc m) hc k (normalizedVector m j)) := by
      exact sub_eq_iff_eq_add.mp h
    rw [← h', smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  have hz : Tendsto (fun k : ℕ => Rk (cc m) hc μ k
      (omegaL m j - Wop (cc m) hc k (normalizedVector m j))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => Rk_norm_le (cc m) hc hμ k _) ?_
    simpa using (omega_sub_W_tendsto hm j).const_mul ((μ + cc m)⁻¹)
  have := ((tendsto_const_nhds (x := normalizedVector m j)).add hz).const_smul
    ((eigenvalue m j + μ)⁻¹)
  simp only [hR]
  simpa using this

theorem resOp_basis {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    resOp hm μ (normalizedVector m j) = (eigenvalue m j + μ)⁻¹ • normalizedVector m j := by
  apply dg_ext (hilbertBasis hm)
  intro i
  rw [resOp, repr_dg _ (bdd_resSym hμ), map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    ← hilbertBasis_apply hm j, HilbertBasis.repr_self]
  by_cases h : i = j
  · subst h; simp [resSym]
  · simp [resSym, h]

end Basis

/-- **Strong resolvent convergence**: the truncated resolvents converge strongly to the spectral
inverse `(B_m+μ)^{-1}`. -/
theorem Rk_tendsto {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : 0 < μ) (u : JacobiL2) :
    Tendsto (fun k : ℕ => Rk (cc m) (cc_nonneg hm) μ k u) atTop (𝓝 (resOp hm μ u)) := by
  have hc := cc_nonneg hm
  have h0 : 0 < μ + cc m := by linarith
  refine tendsto_of_dense_basis (hilbertBasis hm) (C := (μ + cc m)⁻¹) (B := resOp hm μ)
    (fun k => ?_) (fun j => ?_) u
  · exact (Rk (cc m) hc μ k).opNorm_le_bound (inv_nonneg.mpr h0.le)
      (fun f => Rk_norm_le (cc m) hc hμ k f)
  · rw [hilbertBasis_apply, resOp_basis hm hμ j]
    exact Rk_basis_tendsto hm hμ j

theorem resOp_nonneg {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : 0 < μ) {f : JacobiL2} (hf : 0 ≤ f) :
    0 ≤ resOp hm μ f :=
  ge_of_tendsto' (Rk_tendsto hm hμ f) (fun k => Rk_nonneg (cc m) (cc_nonneg hm) hμ k hf)

theorem resOp_le {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : 0 < μ) {f : JacobiL2} (hf : 0 ≤ f) :
    resOp hm μ f ≤ S (μ + cc m) f :=
  le_of_tendsto' (Rk_tendsto hm hμ f) (fun k => Rk_le (cc m) (cc_nonneg hm) hμ k hf)

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
