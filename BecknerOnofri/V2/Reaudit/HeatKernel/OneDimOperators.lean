module

public import BecknerOnofri.V2.Reaudit.HeatKernel.DiagonalCalculus
public import Legacy.BecknerOnofri.JacobiCompleteness
public import Legacy.BecknerOnofri.JacobiHeatKernelAction
public import Legacy.BecknerOnofri.JacobiCircleHeat
public import Legacy.BecknerOnofri.PositiveOperatorNeumann

@[expose] public section

/-! # One-coordinate heat and resolvent operators of `B_m` and their kernels (U05/S015)

Setting.  `JacobiL2 = L²(0,π)`; for `m ≥ 1` the family `b_n = normalizedVector m n` is a Hilbert
basis (`hilbertBasis hm`) of eigenfunctions of `B_m = -d²/dθ² + m(m-1)/sin²θ` with eigenvalues
`(n+m)²` (the repository's identification of the Friedrichs operator with this spectral operator is
`Friedrichs.SpatialSpectralIdentification.operatorGraph_iff_repr`).  The case `m = 1` is the
Dirichlet Laplacian `P_D` on `(0,π)` (sine basis).

This file defines the bounded operators `e^{-tB_m}` and `(B_m+ν)^{-1}` as diagonal operators and
proves:

* the pairing identity `⟪g, e^{-tB_m} f⟫ = ∫ g(x) ∫ K_m(t;x,y) f(y) dy dx`,
* the a.e. integral representation of `e^{-tB_m}` by the eigenfunction-expansion kernel
  `JacobiHeatBounds.heatKernel m t x y`,
* positivity preservation of the Dirichlet heat semigroup (from the positive reflection kernel),
  and of the Dirichlet resolvents (Laplace transform of the heat semigroup).

Nothing here uses the legacy maximum-principle argument for `m ≥ 2`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann

/-- Heat symbol `e^{-tλ_n}` of `B_m`. -/
def heatSym (m : ℕ) (t : ℝ) : ℕ → ℝ := fun n => Real.exp (-t * eigenvalue m n)

/-- Resolvent symbol `(λ_n+ν)^{-1}` of `B_m`. -/
def resSym (m : ℕ) (ν : ℝ) : ℕ → ℝ := fun n => (eigenvalue m n + ν)⁻¹

theorem eigenvalue_nonneg' (m n : ℕ) : 0 ≤ eigenvalue m n := by
  unfold eigenvalue; positivity

theorem abs_heatSym_le {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : |heatSym m t n| ≤ 1 := by
  unfold heatSym
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith [eigenvalue_nonneg' m n]

theorem abs_resSym_le {m : ℕ} {ν : ℝ} (hν : 0 < ν) (n : ℕ) : |resSym m ν n| ≤ ν⁻¹ := by
  unfold resSym
  have h0 : 0 < eigenvalue m n + ν := by linarith [eigenvalue_nonneg' m n]
  rw [abs_of_pos (inv_pos.mpr h0)]
  exact inv_anti₀ hν (by linarith [eigenvalue_nonneg' m n])

theorem bdd_heatSym {m : ℕ} {t : ℝ} (ht : 0 ≤ t) : Bdd (heatSym m t) := ⟨1, abs_heatSym_le ht⟩

theorem bdd_resSym {m : ℕ} {ν : ℝ} (hν : 0 < ν) : Bdd (resSym m ν) := ⟨ν⁻¹, abs_resSym_le hν⟩

/-- `e^{-tB_m}` on `L²(0,π)`. -/
def heatOp {m : ℕ} (hm : 0 < m) (t : ℝ) : JacobiL2 →L[ℝ] JacobiL2 :=
  dg (hilbertBasis hm) (heatSym m t)

/-- `(B_m + ν)^{-1}` on `L²(0,π)`. -/
def resOp {m : ℕ} (hm : 0 < m) (ν : ℝ) : JacobiL2 →L[ℝ] JacobiL2 :=
  dg (hilbertBasis hm) (resSym m ν)

theorem repr_basis {m : ℕ} (hm : 0 < m) (n : ℕ) (u : JacobiL2) :
    (hilbertBasis hm).repr u n = inner ℝ (normalizedVector m n) u := by
  rw [HilbertBasis.repr_apply_apply, hilbertBasis_apply]

theorem inner_basis_eq_integral {m : ℕ} (n : ℕ) (u : JacobiL2) :
    inner ℝ (normalizedVector m n) u = ∫ y, normalizedFunction m n y * u y ∂intervalMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [normalizedVector_ae_eq m n] with y hy
  simp only [hy, RCLike.inner_apply, conj_trivial]
  ring

theorem inner_heatOp_eq_tsum {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) (g f : JacobiL2) :
    inner ℝ g (heatOp hm t f) = ∑' n, heatSym m t n *
      (inner ℝ (normalizedVector m n) g * inner ℝ (normalizedVector m n) f) := by
  rw [← (hilbertBasis hm).tsum_inner_mul_inner g (heatOp hm t f)]
  apply tsum_congr
  intro n
  have h1 : inner ℝ (hilbertBasis hm n) (heatOp hm t f) =
      heatSym m t n * inner ℝ (normalizedVector m n) f := by
    rw [← HilbertBasis.repr_apply_apply, heatOp, repr_dg _ (bdd_heatSym ht), repr_basis hm]
  rw [h1, real_inner_comm (hilbertBasis hm n) g, hilbertBasis_apply]
  ring

theorem inner_resOp_eq_tsum {m : ℕ} (hm : 0 < m) {ν : ℝ} (hν : 0 < ν) (g f : JacobiL2) :
    inner ℝ g (resOp hm ν f) = ∑' n, resSym m ν n *
      (inner ℝ (normalizedVector m n) g * inner ℝ (normalizedVector m n) f) := by
  rw [← (hilbertBasis hm).tsum_inner_mul_inner g (resOp hm ν f)]
  apply tsum_congr
  intro n
  have h1 : inner ℝ (hilbertBasis hm n) (resOp hm ν f) =
      resSym m ν n * inner ℝ (normalizedVector m n) f := by
    rw [← HilbertBasis.repr_apply_apply, resOp, repr_dg _ (bdd_resSym hν), repr_basis hm]
  rw [h1, real_inner_comm (hilbertBasis hm n) g, hilbertBasis_apply]
  ring


/-! ### The kernel action and the pairing identity -/

theorem integrable_L2 (f : JacobiL2) : Integrable (fun y => (f : ℝ → ℝ) y) intervalMeasure :=
  (Lp.memLp f).integrable one_le_two

/-- `x ↦ ∫ K_m(t;x,y) f(y) dy`. -/
def kact (m : ℕ) (t : ℝ) (f : JacobiL2) (x : ℝ) : ℝ :=
  ∫ y, heatKernel m t x y * f y ∂intervalMeasure

/-- The `n`-th term of the spectral expansion of the kernel action. -/
def tm (m : ℕ) (t : ℝ) (f : JacobiL2) (n : ℕ) (x : ℝ) : ℝ :=
  heatSym m t n * normalizedFunction m n x * inner ℝ (normalizedVector m n) f

theorem term_eq (m n : ℕ) (t x : ℝ) (f : JacobiL2) :
    ∫ y, kernelTerm m n t x y * f y ∂intervalMeasure = tm m t f n x := by
  rw [tm, inner_basis_eq_integral]
  simp only [kernelTerm, heatSym, mul_assoc]
  rw [integral_const_mul, integral_const_mul]

theorem tm_bound (m : ℕ) (n : ℕ) {t : ℝ} (ht : 0 < t) (x : ℝ) (f : JacobiL2) :
    ‖tm m t f n x‖ ≤ heatMajorant m 0 t n * ∫ y, ‖(f : ℝ → ℝ) y‖ ∂intervalMeasure := by
  rw [← term_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae (kernelTerm_mul_integrable m n ht x (integrable_L2 f)).norm
    ((integrable_L2 f).norm.const_mul _)
  filter_upwards [] with y
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (kernelTerm_bound m n ht x y) (norm_nonneg _)

theorem kact_eq_tsum (m : ℕ) {t : ℝ} (ht : 0 < t) (f : JacobiL2) (x : ℝ) :
    kact m t f x = ∑' n, tm m t f n x := by
  unfold kact
  rw [kernel_integral_tsum m ht x (integrable_L2 f)]
  exact tsum_congr (fun n => term_eq m n t x f)

theorem tm_continuous (m : ℕ) (t : ℝ) (f : JacobiL2) (n : ℕ) : Continuous (tm m t f n) := by
  unfold tm
  have := (normalizedFunction_contDiff m n).continuous
  fun_prop

theorem summable_tm_bound (m : ℕ) {t : ℝ} (ht : 0 < t) (f : JacobiL2) :
    Summable (fun n => heatMajorant m 0 t n * ∫ y, ‖(f : ℝ → ℝ) y‖ ∂intervalMeasure) :=
  (heatMajorant_summable ht m 0).mul_right _

theorem kact_continuous (m : ℕ) {t : ℝ} (ht : 0 < t) (f : JacobiL2) : Continuous (kact m t f) := by
  have h : kact m t f = fun x => ∑' n, tm m t f n x := funext (kact_eq_tsum m ht f)
  rw [h]
  exact continuous_tsum (tm_continuous m t f) (summable_tm_bound m ht f)
    (fun n x => tm_bound m n ht x f)

theorem kact_bound (m : ℕ) {t : ℝ} (ht : 0 < t) (f : JacobiL2) (x : ℝ) :
    ‖kact m t f x‖ ≤ (∑' n, heatMajorant m 0 t n) * ∫ y, ‖(f : ℝ → ℝ) y‖ ∂intervalMeasure := by
  rw [kact_eq_tsum m ht f x]
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded (summable_tm_bound m ht f).hasSum (fun n => tm_bound m n ht x f)

theorem kact_memLp (m : ℕ) {t : ℝ} (ht : 0 < t) (f : JacobiL2) :
    MemLp (kact m t f) 2 intervalMeasure :=
  MemLp.of_bound (kact_continuous m ht f).aestronglyMeasurable _
    (ae_of_all _ (fun x => kact_bound m ht f x))

/-- **Pairing identity**: `⟪g, e^{-tB_m} f⟫ = ∫ g(x) (∫ K_m(t;x,y) f(y) dy) dx`. -/
theorem integral_mul_kact (m : ℕ) {t : ℝ} (ht : 0 < t) (f g : JacobiL2) :
    ∫ x, g x * kact m t f x ∂intervalMeasure =
      ∑' n, heatSym m t n *
        (inner ℝ (normalizedVector m n) g * inner ℝ (normalizedVector m n) f) := by
  have hgi := integrable_L2 g
  have h1 : ∀ x, g x * kact m t f x = ∑' n, g x * tm m t f n x := fun x => by
    rw [kact_eq_tsum m ht f x, tsum_mul_left]
  simp_rw [h1]
  have hint : ∀ n, Integrable (fun x => g x * tm m t f n x) intervalMeasure := fun n =>
    hgi.mul_bdd (tm_continuous m t f n).aestronglyMeasurable
      (ae_of_all _ (fun x => tm_bound m n ht x f))
  have hsum : Summable (fun n => ∫ x, ‖g x * tm m t f n x‖ ∂intervalMeasure) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => ?_) ((summable_tm_bound m ht f).mul_left (∫ x, ‖(g : ℝ → ℝ) x‖ ∂intervalMeasure))
    calc (∫ x, ‖g x * tm m t f n x‖ ∂intervalMeasure)
        ≤ ∫ x, ‖g x‖ * (heatMajorant m 0 t n * ∫ y, ‖(f : ℝ → ℝ) y‖ ∂intervalMeasure)
            ∂intervalMeasure := by
          apply integral_mono_ae (hint n).norm (hgi.norm.mul_const _)
          filter_upwards [] with x
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (tm_bound m n ht x f) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  apply tsum_congr
  intro n
  have : ∀ x, g x * tm m t f n x = (heatSym m t n * inner ℝ (normalizedVector m n) f) *
      (normalizedFunction m n x * g x) := fun x => by unfold tm; ring
  simp_rw [this]
  rw [integral_const_mul, ← inner_basis_eq_integral]
  ring

/-- `e^{-tB_m}` is the integral operator with the eigenfunction-expansion kernel. -/
theorem heatOp_ae_eq_kact {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) (f : JacobiL2) :
    heatOp hm t f =ᵐ[intervalMeasure] kact m t f := by
  have hmem := kact_memLp m ht f
  have h : heatOp hm t f = hmem.toLp (kact m t f) := by
    apply ext_inner_left ℝ
    intro g
    rw [inner_heatOp_eq_tsum hm ht.le, ← integral_mul_kact m ht f g, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with x hx
    simp only [hx, RCLike.inner_apply, conj_trivial]
    ring
  rw [h]
  exact hmem.coeFn_toLp

theorem heatKernel_continuous_joint (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : ℝ × ℝ => heatKernel m t p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => jointHeat m ![t, p.1, p.2]) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hcmap : Continuous (fun q : ℝ × ℝ => (![t, q.1, q.2] : HeatSpace)) := by fun_prop
    have hA : ContinuousAt (jointHeat m) (![t, p.1, p.2]) :=
      (jointHeat_contDiffAt m (z := ![t, p.1, p.2]) (by simpa using ht)).continuousAt
    exact ContinuousAt.comp (f := fun q : ℝ × ℝ => (![t, q.1, q.2] : HeatSpace)) (x := p) hA
      hcmap.continuousAt
  simpa [jointHeat_eq_heatKernel] using hc

theorem heatKernel_abs_le (m : ℕ) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |heatKernel m t x y| ≤ ∑' n, heatMajorant m 0 t n := by
  have h : heatKernel m t x y = ∑' n, kernelTerm m n t x y := rfl
  rw [h, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded (heatMajorant_summable ht m 0).hasSum
    (fun n => kernelTerm_bound m n ht x y)

/-- Dual-cone criterion for nonnegativity in `L²`. -/
theorem nonneg_of_inner_nonneg (x : JacobiL2) (h : ∀ g : JacobiL2, 0 ≤ g → 0 ≤ inner ℝ g x) :
    Nonnegative intervalMeasure x := by
  set g : JacobiL2 := (-x) ⊔ 0 with hg
  have hg0 : 0 ≤ g := le_sup_right
  have hinner : inner ℝ g x = -(inner ℝ g g) := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sup (-x) 0, Lp.coeFn_neg x, Lp.coeFn_zero ℝ 2 intervalMeasure]
      with a h1 h2 h3
    have hga : (g : ℝ → ℝ) a = max (-(x a)) 0 := by
      rw [hg, h1]
      show max (((-x : JacobiL2) : ℝ → ℝ) a) (((0 : JacobiL2) : ℝ → ℝ) a) = _
      rw [h2, h3]; rfl
    simp only [RCLike.inner_apply, conj_trivial, hga]
    rcases le_total 0 (x a) with hx | hx
    · rw [max_eq_right (by linarith)]; ring
    · rw [max_eq_left (by linarith)]; ring
  have h0 := h g hg0
  rw [hinner, real_inner_self_eq_norm_sq] at h0
  have hn : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
  have hgz : g = 0 := norm_eq_zero.mp hn
  have hx : -x ≤ 0 := by rw [← hgz]; exact le_sup_left
  exact (nonnegative_iff _ x).mpr (by simpa using hx)

theorem heatOp_one_positive {t : ℝ} (ht : 0 < t) : Positive intervalMeasure (heatOp one_pos t) := by
  apply positive_of_integral_kernel intervalMeasure _ (heatKernel 1 t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (heatKernel_one_pos ht hx hy).le
  · intro f
    refine ae_of_all _ (fun x => ?_)
    exact (integrable_L2 f).bdd_mul (heatKernel_continuous_right 1 ht x).aestronglyMeasurable
      (ae_of_all _ (fun y => by rw [Real.norm_eq_abs]; exact heatKernel_abs_le 1 ht x y))
  · intro f
    filter_upwards [heatOp_ae_eq_kact one_pos ht f] with x hx
    exact hx


/-- Positivity of the Dirichlet resolvent: Laplace transform of the positive heat semigroup. -/
theorem resOp_one_positive {ν : ℝ} (hν : 0 < ν) : Positive intervalMeasure (resOp one_pos ν) := by
  intro f hf
  apply nonneg_of_inner_nonneg
  intro g hg
  have hg' : Nonnegative intervalMeasure g := (nonnegative_iff _ g).mpr hg
  set d : ℕ → ℝ := fun n => inner ℝ (normalizedVector 1 n) g with hd
  set c : ℕ → ℝ := fun n => inner ℝ (normalizedVector 1 n) f with hc
  let F : ℕ → ℝ → ℝ := fun n t => (d n * c n) * Real.exp (-(eigenvalue 1 n + ν) * t)
  have hpos : ∀ n, 0 < eigenvalue 1 n + ν := fun n => by linarith [eigenvalue_nonneg' 1 n]
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := fun n =>
    (exp_neg_integrableOn_Ioi 0 (hpos n)).const_mul _
  have hnormint : ∀ n, (∫ t in Ioi (0 : ℝ), ‖F n t‖) = |d n * c n| * (eigenvalue 1 n + ν)⁻¹ := by
    intro n
    have : ∀ t, ‖F n t‖ = |d n * c n| * Real.exp (-(eigenvalue 1 n + ν) * t) := fun t => by
      simp only [F, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul]
    simp_rw [this]
    rw [integral_const_mul]
    have h := integral_exp_mul_Ioi (a := -(eigenvalue 1 n + ν)) (by linarith [hpos n]) 0
    simp only [mul_zero, Real.exp_zero] at h
    rw [h]
    field_simp
  have hFsum : Summable (fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖) := by
    have hs : Summable (fun n => |d n * c n|) :=
      ((hilbertBasis (one_pos : 0 < 1)).summable_inner_mul_inner g f).abs.congr (fun n => by
        simp only [hd, hc, hilbertBasis_apply, real_inner_comm g]) |> fun h => h
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun t => norm_nonneg _)) (fun n => ?_)
      (hs.mul_right ν⁻¹)
    rw [hnormint]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hν (by linarith [eigenvalue_nonneg' 1 n]))
      (abs_nonneg _)
  have hlap : inner ℝ g (resOp one_pos ν f) = ∫ t in Ioi (0 : ℝ), ∑' n, F n t := by
    rw [inner_resOp_eq_tsum one_pos hν, ← integral_tsum_of_summable_integral_norm hFint hFsum]
    apply tsum_congr
    intro n
    have h := integral_exp_mul_Ioi (a := -(eigenvalue 1 n + ν)) (by linarith [hpos n]) 0
    simp only [mul_zero, Real.exp_zero] at h
    simp only [F]
    rw [integral_const_mul, h, resSym]
    simp only [hd, hc]
    field_simp
  rw [hlap]
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have h1 : ∑' n, F n t = Real.exp (-ν * t) * inner ℝ g (heatOp one_pos t f) := by
    rw [inner_heatOp_eq_tsum one_pos ht'.le, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [F, heatSym, hd, hc]
    rw [show -(eigenvalue 1 n + ν) * t = -ν * t + (-t * eigenvalue 1 n) by ring, Real.exp_add]
    ring
  rw [h1]
  apply mul_nonneg (Real.exp_pos _).le
  have hH : Nonnegative intervalMeasure (heatOp one_pos t f) := heatOp_one_positive ht' f hf
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hg', hH] with a ha hb
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_nonneg hb ha

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
