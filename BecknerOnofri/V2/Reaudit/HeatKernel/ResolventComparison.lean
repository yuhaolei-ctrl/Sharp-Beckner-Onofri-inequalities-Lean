module

public import BecknerOnofri.V2.Reaudit.HeatKernel.OneDimOperators
public import Legacy.BecknerOnofri.BoundedL2Multiplier
public import Legacy.BecknerOnofri.JacobiNeumann

@[expose] public section

/-! # Resolvent comparison for `B_m = P_D + V_m` by truncated potentials (U05/S015, steps 4)

Printed route (`eq:potential-kernel-domination`): `V_{α,k} = min(V_α, k)`, domination of the semigroup of
`P_D + V_{α,k}` by that of `P_D` (Trotter + positivity of `e^{-tV_{α,k}/n}`), then the limit
`k → ∞` by monotone convergence of forms.  Here the same two steps are carried out on the explicit
eigenbasis, in resolvent form:

1. With `c = m(m-1)` and `W = V - c = c cot²`, `W_k = min(W,k)`: the resolvent of `P_D + c + W_k` is
   `(I - S_k (k - W_k))^{-1} S_k`, `S_k = (P_D + μ + c + k)^{-1}`, a norm-convergent Neumann series of
   positive operators (`‖S_k (k-W_k)‖ ≤ k/(μ+c+k) < 1`).  It is positive, and
   `S_0 f - R_k f = S_0 W_k R_k f ≥ 0` for `f ≥ 0` (resolvent identity).
2. Uniform bound `‖R_k‖ ≤ (μ+c)^{-1}` from positivity, and `R_k φ_j → (λ_j+μ)^{-1} φ_j` on every
   eigenfunction `φ_j` of `B_m`: `φ_j` is smooth, vanishes at `0, π`, and
   `W φ_j = (λ_j - c)φ_j + φ_j''` is bounded and continuous (the eigenvalue equation); two integrations by
   parts against the sine basis give `φ_j = S_0((λ_j+μ)φ_j - Wφ_j)`.  Totality of the eigenbasis then
   gives strong convergence `R_k → (B_m+μ)^{-1}` where `(B_m+μ)^{-1}` is the repository's spectral operator.
3. Hence `0 ≤ (B_m+μ)^{-1} f ≤ (P_D + μ + m(m-1))^{-1} f` for `f ≥ 0`.

Nothing from the legacy parabolic maximum principle is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri Legacy.BecknerOnofri.JacobiEigenfunctions
  Legacy.BecknerOnofri.JacobiHeatBounds Legacy.BecknerOnofri.JacobiHeatPositivity
  Legacy.BecknerOnofri.PositiveOperatorNeumann Legacy.BecknerOnofri.BoundedL2Multiplier

/-! ### Truncated potentials -/

/-- `c cot²θ`, the part `V - c` of the potential `V = c/sin²θ`. -/
def cot2 (c x : ℝ) : ℝ := c * (Real.cos x / Real.sin x) ^ 2

theorem cot2_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ cot2 c x := mul_nonneg hc (sq_nonneg _)

/-- The truncation `min(c cot², k)`. -/
def cotTrunc (c : ℝ) (k : ℕ) (x : ℝ) : ℝ := min (cot2 c x) k

theorem cotTrunc_nonneg {c : ℝ} (hc : 0 ≤ c) (k : ℕ) (x : ℝ) : 0 ≤ cotTrunc c k x :=
  le_min (cot2_nonneg hc x) (Nat.cast_nonneg k)

theorem cotTrunc_le (c : ℝ) (k : ℕ) (x : ℝ) : cotTrunc c k x ≤ k := min_le_right _ _

theorem cotTrunc_le_cot2 (c : ℝ) (k : ℕ) (x : ℝ) : cotTrunc c k x ≤ cot2 c x := min_le_left _ _

theorem measurable_cot2 (c : ℝ) : Measurable (cot2 c) :=
  measurable_const.mul ((Real.measurable_cos.div Real.measurable_sin).pow_const 2)

theorem measurable_cotTrunc (c : ℝ) (k : ℕ) : Measurable (cotTrunc c k) :=
  (measurable_cot2 c).min measurable_const

/-- The truncated potential as a bounded weight. -/
def wt (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Weight intervalMeasure where
  value := cotTrunc c k
  measurable := (measurable_cotTrunc c k).aestronglyMeasurable
  bound := k
  nonneg_bound := Nat.cast_nonneg k
  bounded := ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cotTrunc_nonneg hc k x)]
    exact cotTrunc_le c k x)

/-- The complementary bounded weight `k - W_k ∈ [0,k]`. -/
def ut (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Weight intervalMeasure where
  value := fun x => (k : ℝ) - cotTrunc c k x
  measurable := (measurable_const.sub (measurable_cotTrunc c k)).aestronglyMeasurable
  bound := k
  nonneg_bound := Nat.cast_nonneg k
  bounded := ae_of_all _ (fun x => by
    have h0 := cotTrunc_nonneg hc k x
    have h1 := cotTrunc_le c k x
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith)

/-- Multiplication by `W_k`. -/
def Wop (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Operator intervalMeasure := (wt c hc k).operator

/-- Multiplication by `k - W_k`. -/
def Uop (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Operator intervalMeasure := (ut c hc k).operator

theorem Uop_apply (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (u : JacobiL2) :
    Uop c hc k u = (k : ℝ) • u - Wop c hc k u := by
  apply Lp.ext
  filter_upwards [(ut c hc k).operator_ae u, (wt c hc k).operator_ae u,
    Lp.coeFn_sub ((k : ℝ) • u) (Wop c hc k u), Lp.coeFn_smul (k : ℝ) u] with x h1 h2 h3 h4
  have h1' : Uop c hc k u x = ((k : ℝ) - cotTrunc c k x) * u x := h1
  have h2' : Wop c hc k u x = cotTrunc c k x * u x := h2
  rw [h1', h3, Pi.sub_apply, h4, Pi.smul_apply, h2', smul_eq_mul]
  ring

theorem Wop_positive (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Positive intervalMeasure (Wop c hc k) :=
  (wt c hc k).operator_positive (ae_of_all _ (cotTrunc_nonneg hc k))

theorem Uop_positive (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : Positive intervalMeasure (Uop c hc k) :=
  (ut c hc k).operator_positive (ae_of_all _ (fun x => by
    have h0 := cotTrunc_nonneg hc k x
    have h1 := cotTrunc_le c k x
    show 0 ≤ (k : ℝ) - cotTrunc c k x
    linarith))

theorem Uop_norm_le (c : ℝ) (hc : 0 ≤ c) (k : ℕ) : ‖Uop c hc k‖ ≤ k :=
  (ut c hc k).operator_norm_le

/-! ### Dirichlet resolvents -/

/-- `(P_D + ν)^{-1}` on `L²(0,π)`. -/
abbrev S (ν : ℝ) : Operator intervalMeasure := resOp (one_pos : 0 < 1) ν

theorem S_positive {ν : ℝ} (hν : 0 < ν) : Positive intervalMeasure (S ν) := resOp_one_positive hν

theorem S_norm_le {ν : ℝ} (hν : 0 < ν) : ‖S ν‖ ≤ ν⁻¹ :=
  dg_norm_le _ (inv_nonneg.mpr hν.le) (abs_resSym_le hν)

theorem repr_S {ν : ℝ} (hν : 0 < ν) (u : JacobiL2) (n : ℕ) :
    (hilbertBasis (one_pos : 0 < 1)).repr (S ν u) n =
      (eigenvalue 1 n + ν)⁻¹ * (hilbertBasis (one_pos : 0 < 1)).repr u n :=
  repr_dg _ (bdd_resSym hν) u n

theorem S_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : JacobiL2) :
    S a u - S b u = (b - a) • S a (S b u) := by
  apply dg_ext (hilbertBasis (one_pos : 0 < 1))
  intro n
  have h1 := eigenvalue_nonneg' 1 n
  have ha' : 0 < eigenvalue 1 n + a := by linarith
  have hb' : 0 < eigenvalue 1 n + b := by linarith
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    repr_S ha, repr_S hb, repr_S ha, repr_S hb]
  field_simp
  ring

theorem S_comm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (u : JacobiL2) :
    S a (S b u) = S b (S a u) := by
  apply dg_ext (hilbertBasis (one_pos : 0 < 1))
  intro n
  rw [repr_S ha, repr_S hb, repr_S hb, repr_S ha]
  ring

/-! ### The truncated resolvent -/

section Truncated
variable (c : ℝ) (hc : 0 ≤ c)

/-- `T_k = S_k (k - W_k)` with `S_k = (P_D + μ + c + k)^{-1}`. -/
def Tk (μ : ℝ) (k : ℕ) : Operator intervalMeasure :=
  (S (μ + c + k)).comp (Uop c hc k)

theorem Tk_positive {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : Positive intervalMeasure (Tk c hc μ k) := by
  intro f hf
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact S_positive (by linarith) _ (Uop_positive c hc k f hf)

theorem Tk_norm_lt_one {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : ‖Tk c hc μ k‖ < 1 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hν : 0 < μ + c + k := by linarith
  calc ‖Tk c hc μ k‖ ≤ ‖S (μ + c + k)‖ * ‖Uop c hc k‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (μ + c + k)⁻¹ * k :=
        mul_le_mul (S_norm_le hν) (Uop_norm_le c hc k) (norm_nonneg _) (inv_nonneg.mpr hν.le)
    _ < 1 := by
        rw [inv_mul_lt_iff₀ hν]
        linarith

/-- The truncated resolvent `(P_D + c + W_k + μ)^{-1} = (I - T_k)^{-1} S_k`. -/
def Rk (μ : ℝ) (k : ℕ) : Operator intervalMeasure :=
  (neumannOperator intervalMeasure (Tk c hc μ k)).comp (S (μ + c + k))

theorem Rk_positive {μ : ℝ} (hμ : 0 < μ) (k : ℕ) : Positive intervalMeasure (Rk c hc μ k) := by
  intro f hf
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact neumann_nonnegative intervalMeasure (Tk_positive c hc hμ k) (Tk_norm_lt_one c hc hμ k)
    (S_positive (by linarith) f hf)

theorem Rk_spec {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (f : JacobiL2) :
    Rk c hc μ k f - Tk c hc μ k (Rk c hc μ k f) = S (μ + c + k) f :=
  neumann_right_inverse intervalMeasure (Tk_norm_lt_one c hc hμ k) (S (μ + c + k) f)

theorem Tk_apply (μ : ℝ) (k : ℕ) (u : JacobiL2) :
    Tk c hc μ k u = (k : ℝ) • S (μ + c + k) u - S (μ + c + k) (Wop c hc k u) := by
  simp only [Tk, ContinuousLinearMap.comp_apply, Uop_apply, map_sub, map_smul]

/-- Resolvent identity: `R_k f = S_0 (f - W_k R_k f)`. -/
theorem Rk_eq {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (f : JacobiL2) :
    Rk c hc μ k f = S (μ + c) (f - Wop c hc k (Rk c hc μ k f)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hn0 : 0 < μ + c := by linarith
  have hnk : 0 < μ + c + k := by linarith
  set u := Rk c hc μ k f with hu
  have hspec := Rk_spec c hc hμ k f
  rw [← hu] at hspec
  have hT := Tk_apply c hc μ k u
  have h1 : u = S (μ + c + k) (f + (k : ℝ) • u - Wop c hc k u) := by
    rw [hT] at hspec
    simp only [map_add, map_sub, map_smul]
    rw [← hspec]
    abel
  have h2 := S_sub hn0 hnk (f + (k : ℝ) • u - Wop c hc k u)
  rw [← h1, show μ + c + (k : ℝ) - (μ + c) = k by ring] at h2
  have h3 : f + (k : ℝ) • u - Wop c hc k u = (f - Wop c hc k u) + (k : ℝ) • u := by abel
  rw [h3] at h2
  simp only [map_add, map_smul] at h2
  have h4 : S (μ + c) (f - Wop c hc k u) = u := by
    have h5 : S (μ + c) (f - Wop c hc k u) + (k : ℝ) • S (μ + c) u - u = (k : ℝ) • S (μ + c) u :=
      h2
    have h6 : S (μ + c) (f - Wop c hc k u) - u = 0 := by
      have e : S (μ + c) (f - Wop c hc k u) - u =
          (S (μ + c) (f - Wop c hc k u) + (k : ℝ) • S (μ + c) u - u) - (k : ℝ) • S (μ + c) u := by
        abel
      rw [e]; exact sub_eq_zero.mpr h5
    exact sub_eq_zero.mp h6
  exact h4.symm

theorem Rk_nonneg {μ : ℝ} (hμ : 0 < μ) (k : ℕ) {f : JacobiL2} (hf : 0 ≤ f) :
    0 ≤ Rk c hc μ k f :=
  (nonnegative_iff _ _).mp (Rk_positive c hc hμ k f ((nonnegative_iff _ _).mpr hf))

theorem Rk_le {μ : ℝ} (hμ : 0 < μ) (k : ℕ) {f : JacobiL2} (hf : 0 ≤ f) :
    Rk c hc μ k f ≤ S (μ + c) f := by
  have hn0 : 0 < μ + c := by linarith
  have hu := Rk_nonneg c hc hμ k hf
  have hW : 0 ≤ Wop c hc k (Rk c hc μ k f) :=
    (nonnegative_iff _ _).mp (Wop_positive c hc k _ ((nonnegative_iff _ _).mpr hu))
  have hS : 0 ≤ S (μ + c) (Wop c hc k (Rk c hc μ k f)) :=
    (nonnegative_iff _ _).mp (S_positive hn0 _ ((nonnegative_iff _ _).mpr hW))
  have h := Rk_eq c hc hμ k f
  rw [map_sub] at h
  have h' := h
  rw [eq_sub_iff_add_eq] at h'
  have : S (μ + c) f - Rk c hc μ k f = S (μ + c) (Wop c hc k (Rk c hc μ k f)) := by
    rw [← h']; abel
  rw [← this] at hS
  exact sub_nonneg.mp hS

/-- Uniform bound from positivity: `‖R_k f‖ ≤ (μ+c)^{-1} ‖f‖`. -/
theorem Rk_norm_le {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (f : JacobiL2) :
    ‖Rk c hc μ k f‖ ≤ (μ + c)⁻¹ * ‖f‖ := by
  have hn0 : 0 < μ + c := by linarith
  set h : JacobiL2 := |f| with hh
  have hh0 : 0 ≤ h := abs_nonneg f
  have hRh := Rk_nonneg c hc hμ k hh0
  have hRh' := Rk_le c hc hμ k hh0
  have h1 : 0 ≤ Rk c hc μ k h - Rk c hc μ k f := by
    rw [← map_sub]; exact Rk_nonneg c hc hμ k (sub_nonneg.mpr (le_abs_self f))
  have h2 : 0 ≤ Rk c hc μ k h + Rk c hc μ k f := by
    rw [← map_add]; exact Rk_nonneg c hc hμ k (by
      show 0 ≤ |f| + f
      have h' := sub_nonneg.mpr (neg_le_abs f)
      rwa [sub_neg_eq_add] at h')
  have hnorm : ‖h‖ = ‖f‖ := by
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_abs f] with x hx
      rw [hh, hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_abs f] with x hx
      rw [hh, hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  calc ‖Rk c hc μ k f‖ ≤ ‖Rk c hc μ k h‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(Lp.coeFn_nonneg _).mpr h1, (Lp.coeFn_nonneg _).mpr h2,
          Lp.coeFn_sub (Rk c hc μ k h) (Rk c hc μ k f),
          Lp.coeFn_add (Rk c hc μ k h) (Rk c hc μ k f)] with x a1 a2 a3 a4
        rw [Pi.zero_apply] at a1 a2
        rw [a3, Pi.sub_apply] at a1
        rw [a4, Pi.add_apply] at a2
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ (Rk c hc μ k h) x)]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ ≤ ‖S (μ + c) h‖ := by
        apply Lp.norm_le_norm_of_ae_le
        filter_upwards [(Lp.coeFn_nonneg _).mpr hRh, (Lp.coeFn_le _ _).mpr hRh'] with x a1 a2
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg a1, abs_of_nonneg (a1.trans a2)]
        exact a2
    _ ≤ (μ + c)⁻¹ * ‖h‖ := by
        have := (S (μ + c)).le_opNorm h
        exact this.trans (mul_le_mul_of_nonneg_right (S_norm_le hn0) (norm_nonneg _))
    _ = (μ + c)⁻¹ * ‖f‖ := by rw [hnorm]

end Truncated

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
