module

public import BecknerOnofri.V2.Reaudit.HeatKernel.DirichletSemigroup

@[expose] public section

/-! # Heat kernels on `Ω_α`, coordinate product formula and the strict comparison chain

For `S ⊆ Fin d` let `Ω_S = (0,1/2)^S × (ℝ/ℤ)^{S^c}` (the domain `Ω_α` of `lem:fractional` for
`S = S_α`).  The heat kernel of `P_{D_S}` (Dirichlet Laplacian in the coordinates of `S`,
periodic in the others) is the product of the one-coordinate kernels
(`eq:several-coordinate-strict-kernel`, the "coordinate product formula").  We define it as that
product, with the Dirichlet factor `dirichletKernel` of `DirichletKernel.lean` and the periodic
factor `circleKernel`, and prove:

* strict positivity on `Ω_S × Ω_S` (`eq:dirichlet-heat-positive`);
* for `i ∈ S`, `S ≠ {i}`: strict domination of `p_{P_{D_S}}` by `p_{P_{D_i}}`
  (`eq:several-coordinate-strict-kernel`, last inequality);
* the elementary comparison used for the one-coordinate case (`eq:one-coordinate-strict-kernel`).

What is **not** here: the domination `p_{B_α} ≤ p_{P_{D_S}}` by Trotter's product formula and
monotone convergence of forms (`eq:potential-kernel-domination`), which concerns the Friedrichs
operator `B_α = P_{D_S} + V_α` with the singular potential; it enters downstream results only as
an explicitly named hypothesis.
-/

noncomputable section
open Set Finset
open scoped Real
namespace BecknerOnofri.V2.Reaudit.HeatKernel

variable {d : ℕ}

/-- The heat kernel of `P_{D_S}` on `Ω_S`: Dirichlet factors for the coordinates in `S`, periodic
factors for the others (the coordinate product formula). -/
def mixedKernel (S : Finset (Fin d)) (t : ℝ) (x x' : Fin d → ℝ) : ℝ :=
  ∏ j, if j ∈ S then dirichletKernel t (x j) (x' j) else circleKernel t (x j - x' j)

/-- The coordinates of `S` lie in the open half-period `(0,1/2)`: `x ∈ Ω_S`. -/
def InOmega (S : Finset (Fin d)) (x : Fin d → ℝ) : Prop :=
  ∀ j ∈ S, x j ∈ Ioo (0 : ℝ) (1 / 2)

/-- `eq:dirichlet-heat-positive`: strict positivity of the heat kernel of `P_{D_S}` on `Ω_S`. -/
theorem mixedKernel_pos {S : Finset (Fin d)} {t : ℝ} (ht : 0 < t) {x x' : Fin d → ℝ}
    (hx : InOmega S x) (hx' : InOmega S x') : 0 < mixedKernel S t x x' := by
  unfold mixedKernel
  apply Finset.prod_pos
  intro j _
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    exact dirichletKernel_pos ht (hx j hj) (hx' j hj)
  · rw [if_neg hj]
    exact circleKernel_pos ht _

/-- The periodic factor dominates the Dirichlet factor coordinatewise, hence
`p_{P_{D_S}} ≤ p_{P_{D_{S'}}}` for `S' ⊆ S` on `Ω_S` (Dirichlet conditions only lower the kernel). -/
theorem mixedKernel_le_of_subset {S S' : Finset (Fin d)} (hSS : S' ⊆ S) {t : ℝ} (ht : 0 < t)
    {x x' : Fin d → ℝ} (hx : InOmega S x) (hx' : InOmega S x') :
    mixedKernel S t x x' ≤ mixedKernel S' t x x' := by
  unfold mixedKernel
  apply Finset.prod_le_prod₀
  · intro j _
    by_cases hj : j ∈ S
    · rw [if_pos hj]
      exact (dirichletKernel_pos ht (hx j hj) (hx' j hj)).le
    · rw [if_neg hj]
      exact (circleKernel_pos ht _).le
  · intro j _
    by_cases hj' : j ∈ S'
    · rw [if_pos hj', if_pos (hSS hj')]
    · rw [if_neg hj']
      by_cases hj : j ∈ S
      · rw [if_pos hj]
        exact (dirichletKernel_lt_circleKernel ht _ _).le
      · rw [if_neg hj]

/-- **`eq:several-coordinate-strict-kernel`** (last inequality): if `S` has at least two
elements and `i ∈ S`, the heat kernel of `P_{D_S}` is strictly below that of `P_{D_{\{i\}}}` on
`Ω_S × Ω_S`; the strictness comes from a second Dirichlet coordinate through the reflection
comparison `p_t^D(a,b) < p_t^{per}(a-b)`. -/
theorem mixedKernel_lt_single {S : Finset (Fin d)} {i j : Fin d} (hi : i ∈ S) (hj : j ∈ S)
    (hij : j ≠ i) {t : ℝ} (ht : 0 < t) {x x' : Fin d → ℝ} (hx : InOmega S x)
    (hx' : InOmega S x') : mixedKernel S t x x' < mixedKernel {i} t x x' := by
  unfold mixedKernel
  apply Finset.prod_lt_prod₀
  · intro k _
    by_cases hk : k ∈ S
    · rw [if_pos hk]
      exact dirichletKernel_pos ht (hx k hk) (hx' k hk)
    · rw [if_neg hk]
      exact circleKernel_pos ht _
  · intro k _
    by_cases hk' : k ∈ ({i} : Finset (Fin d))
    · rw [if_pos hk']
      have : k = i := Finset.mem_singleton.mp hk'
      subst this
      rw [if_pos hi]
    · rw [if_neg hk']
      by_cases hk : k ∈ S
      · rw [if_pos hk]
        exact (dirichletKernel_lt_circleKernel ht _ _).le
      · rw [if_neg hk]
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    have hj' : j ∉ ({i} : Finset (Fin d)) := by simpa using hij
    rw [if_pos hj, if_neg hj']
    exact dirichletKernel_lt_circleKernel ht _ _

/-- `eq:one-coordinate-strict-kernel`, the elementary step: a kernel dominated by
`e^{-ct} p` with `c > 0` and `p > 0` is strictly below `p`. -/
theorem lt_of_le_exp_mul {q p c t : ℝ} (hc : 0 < c) (ht : 0 < t) (hp : 0 < p)
    (hq : q ≤ Real.exp (-c * t) * p) : q < p := by
  have h1 : Real.exp (-c * t) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  calc q ≤ Real.exp (-c * t) * p := hq
    _ < 1 * p := mul_lt_mul_of_pos_right h1 hp
    _ = p := one_mul p

end BecknerOnofri.V2.Reaudit.HeatKernel
