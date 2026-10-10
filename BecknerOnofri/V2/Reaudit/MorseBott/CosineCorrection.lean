module

public import BecknerOnofri.LocalElevenCore.QuadraticSlavingBridge
public import BecknerOnofri.LocalElevenCore.SobolevQuadraticTrustedBridge
public import BecknerOnofri.LocalElevenCore.DirectionalSobolevSlaving

@[expose] public section

/-! # The displayed cosine correction `(5.full-branch-w2)`

The quadratic slaving term of the Lyapunov--Schmidt graph is
`w_2(v) = 1/2 ((2π)^{-d}(-Δ)^{d/2} - Id)^{-1} P_{K^⊥}(v²)` (`eq:section5-quadratic-slaving`).
In the repository this is `LocalEleven.QuadraticSlaving.quadraticCorrection hd z`, with the
first-shell coordinates `z : Fin d → ℂ` and `v = assembly d z = Σ_j 2 Re (z_j e^{2π i x_j})`.
Here the diagonal complement inverse is applied to the explicit finite expansion of `P_{K^⊥}(v²)`
and the displayed trigonometric polynomial is obtained. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexConjugate

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven ContinuousGibbs ContinuousFirstShell
open BecknerOnofri.HighDim.LocalEleven.QuadraticModes
open BecknerOnofri.HighDim.LocalEleven.QuadraticSlaving (quadraticCorrection sliceCorrection
  correction_directional_sobolev)

/-- The resolvent acts on a complement mode by the scalar `1/(|k|^d - 1)`. -/
theorem resolvent_complementMap_synthesis {d : ℕ} (hd : 11 ≤ d) {k : Frequency d}
    (hk : ComplementFrequency k) (w : ℂ) :
    ((resolvent hd (complementMap d (synthesis k w)) : complement d) : Space d) =
      (1 / (frequencyLength k ^ d - 1)) • synthesis k w := by
  rw [complementMap_synthesis hk, resolvent_synthesis hd hk]
  rfl

/-- The diagonal term: `(2e_i) ↦ 1/(2^d-1)`. -/
theorem resolvent_double {d : ℕ} (hd : 11 ≤ d) (i : Fin d) (w : ℂ) :
    ((resolvent hd (complementMap d (synthesis (axisFrequency i + axisFrequency i) w)) :
      complement d) : Space d) =
      (1 / ((2 : ℝ) ^ d - 1)) • synthesis (axisFrequency i + axisFrequency i) w := by
  rw [resolvent_complementMap_synthesis hd (HighDim.QuadraticModes.complement_double i), HighDim.QuadraticModes.eigenvalue_double]

theorem resolvent_sum {d : ℕ} (hd : 11 ≤ d) {i j : Fin d} (hij : i ≠ j) (w : ℂ) :
    ((resolvent hd (complementMap d (synthesis (axisFrequency i + axisFrequency j) w)) :
      complement d) : Space d) =
      (1 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) • synthesis (axisFrequency i + axisFrequency j) w := by
  rw [resolvent_complementMap_synthesis hd (HighDim.QuadraticModes.complement_sum hij), HighDim.QuadraticModes.eigenvalue_sum hij]

theorem resolvent_diff {d : ℕ} (hd : 11 ≤ d) {i j : Fin d} (hij : i ≠ j) (w : ℂ) :
    ((resolvent hd (complementMap d (synthesis (axisFrequency i - axisFrequency j) w)) :
      complement d) : Space d) =
      (1 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) • synthesis (axisFrequency i - axisFrequency j) w := by
  rw [resolvent_complementMap_synthesis hd (HighDim.QuadraticModes.complement_diff hij), HighDim.QuadraticModes.eigenvalue_diff hij]


/-- `axisFrequency i` is the `i`-th unit vector. -/
theorem axisFrequency_eq_single {d : ℕ} (i : Fin d) : axisFrequency i = Pi.single i 1 := by
  funext l
  by_cases h : l = i <;> simp [axisFrequency, h]

theorem mFourier_axis {d : ℕ} (i : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency i) x = fourier 1 (x i) := by
  rw [axisFrequency_eq_single, UnitAddTorus.mFourier_single]

theorem mFourier_axis_add {d : ℕ} (i j : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency i + axisFrequency j) x =
      fourier 1 (x i) * fourier 1 (x j) := by
  rw [UnitAddTorus.mFourier_add, mFourier_axis, mFourier_axis]

theorem mFourier_axis_sub {d : ℕ} (i j : Fin d) (x : Torus d) :
    UnitAddTorus.mFourier (axisFrequency i - axisFrequency j) x =
      fourier 1 (x i) * conj (fourier 1 (x j)) := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg, mFourier_axis,
    mFourier_axis]

/-- One summand of the finite expansion of `w_2`. -/
def term {d : ℕ} (z : Coordinates d) (x : Torus d) (i j : Fin d) : ℝ :=
  if i = j then (1 / ((2 : ℝ) ^ d - 1)) *
      (z i * z i * (fourier 1 (x i) * fourier 1 (x i))).re
  else (1 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) *
      ((z i * z j * (fourier 1 (x i) * fourier 1 (x j))).re +
        (z i * conj (z j) * (fourier 1 (x i) * conj (fourier 1 (x j)))).re)

/-- **Exact pointwise form of the quadratic slaving term**: applying the diagonal complement
inverse to the finite Fourier expansion of `P_{K^⊥}(v²)`. -/
theorem quadraticCorrection_apply {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) (x : Torus d) :
    ((quadraticCorrection hd z : complement d) : Space d) x = ∑ i, ∑ j, term z x i j := by
  rw [quadraticCorrection_eq_resolvent, quadraticSource_expansion]
  simp only [map_sum, Submodule.coe_smul, Submodule.coe_sum, ContinuousMap.smul_apply,
    ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hij : i = j
  · subst hij
    simp only [term, ↓reduceIte, sub_self, complementMap_synthesis_zero, add_zero]
    rw [resolvent_double hd]
    simp only [ContinuousMap.smul_apply, synthesis_apply, smul_eq_mul, mFourier_axis_add]
    ring
  · simp only [term, hij, ↓reduceIte, map_add, Submodule.coe_add]
    rw [resolvent_sum hd hij, resolvent_diff hd hij]
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, synthesis_apply, smul_eq_mul,
      mFourier_axis_add, mFourier_axis_sub]
    ring


/-- The point of the torus with real coordinates `t`. -/
def cosLift {d : ℕ} (t : Fin d → ℝ) : Torus d := fun j => ((t j : ℝ) : UnitAddCircle)

/-- First-shell coordinates of the leading term `2 √r Σ_j cos (2π (x_j - s_j))`:
`z_j = √r e^{-2π i s_j}`. -/
def leadingCoordinates {d : ℕ} (r : ℝ) (s : Fin d → ℝ) : Coordinates d :=
  fun j => (Real.sqrt r : ℂ) * Complex.exp (-(2 * Real.pi * s j : ℝ) * Complex.I)

theorem fourier_one_lift (t : ℝ) :
    fourier 1 ((t : ℝ) : UnitAddCircle) = Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem exp_mul_I_eq (θ : ℝ) :
    Complex.exp ((θ : ℝ) * Complex.I) = ⟨Real.cos θ, Real.sin θ⟩ := by
  apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem leading_mul_fourier {d : ℕ} (r : ℝ) (s t : Fin d → ℝ) (i : Fin d) :
    leadingCoordinates r s i * fourier 1 (cosLift (fun j => t j + s j) i) =
      ⟨Real.sqrt r * Real.cos (2 * Real.pi * t i), Real.sqrt r * Real.sin (2 * Real.pi * t i)⟩ := by
  unfold leadingCoordinates cosLift
  rw [fourier_one_lift, mul_assoc, ← Complex.exp_add]
  have : (-(2 * Real.pi * s i : ℝ) : ℂ) * Complex.I + ((2 * Real.pi * (t i + s i) : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * t i : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, exp_mul_I_eq]
  apply Complex.ext <;> simp


theorem term_eval {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (s t : Fin d → ℝ) (i j : Fin d) :
    term (leadingCoordinates r s) (cosLift (fun j => t j + s j)) i j =
      if i = j then r / ((2 : ℝ) ^ d - 1) * Real.cos (4 * Real.pi * t i)
      else 2 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) *
        (Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j)) := by
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr
  set z := leadingCoordinates r s with hz
  set x := cosLift (fun j => t j + s j) with hx
  by_cases hij : i = j
  · subst hij
    have h1 : z i * z i * (fourier 1 (x i) * fourier 1 (x i)) =
        (z i * fourier 1 (x i)) * (z i * fourier 1 (x i)) := by ring
    simp only [term, ↓reduceIte]
    rw [h1, hz, hx, leading_mul_fourier]
    have hc := Real.cos_two_mul (2 * Real.pi * t i)
    have hs := Real.sin_sq_add_cos_sq (2 * Real.pi * t i)
    have h4 : Real.cos (4 * Real.pi * t i) = Real.cos (2 * Real.pi * t i) ^ 2 -
        Real.sin (2 * Real.pi * t i) ^ 2 := by
      have : 4 * Real.pi * t i = 2 * (2 * Real.pi * t i) := by ring
      rw [this]; nlinarith
    rw [h4]
    simp only [Complex.mul_re]
    linear_combination (1 / ((2 : ℝ) ^ d - 1)) *
      (Real.cos (2 * Real.pi * t i) ^ 2 - Real.sin (2 * Real.pi * t i) ^ 2) * hsq
  · have h1 : z i * z j * (fourier 1 (x i) * fourier 1 (x j)) =
        (z i * fourier 1 (x i)) * (z j * fourier 1 (x j)) := by ring
    have h2 : z i * conj (z j) * (fourier 1 (x i) * conj (fourier 1 (x j))) =
        (z i * fourier 1 (x i)) * conj (z j * fourier 1 (x j)) := by
      rw [map_mul]; ring
    simp only [term, hij, ↓reduceIte]
    rw [h1, h2, hz, hx, leading_mul_fourier, leading_mul_fourier]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    linear_combination (1 / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) *
      (2 * Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j)) * hsq


/-- Off-diagonal double sums of a symmetric array are twice the sum over `i < j`. -/
theorem offDiag_sum_eq {d : ℕ} (g : Fin d → Fin d → ℝ) (hg : ∀ i j, g i j = g j i) :
    ∑ i, ∑ j, (if i = j then 0 else g i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, g i j := by
  have h1 : ∀ i j : Fin d, (if i = j then (0:ℝ) else g i j) =
      (if i < j then g i j else 0) + (if j < i then g j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hg i j]
  have h2 : ∀ i, ∑ j ∈ Finset.Ioi i, g i j = ∑ j, (if i < j then g i j else 0) := by
    intro i
    rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  simp only [h1, Finset.sum_add_distrib, h2]
  rw [Finset.sum_comm (f := fun i j => if j < i then g j i else 0)]
  ring

/-- The leading term `v = Σ_j 2 √r cos (2π (x_j - s_j))`, evaluated at `x = t + s`. -/
theorem assembly_leading_apply {d : ℕ} (r : ℝ) (s t : Fin d → ℝ) :
    (assembly d (leadingCoordinates r s) : Space d) (cosLift (fun j => t j + s j)) =
      2 * Real.sqrt r * ∑ j, Real.cos (2 * Real.pi * t j) := by
  rw [assembly_apply]
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, synthesis_apply, mFourier_axis,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [leading_mul_fourier]
  simp only
  ring

/-- **The displayed cosine correction `(5.full-branch-w2)`.**  With the leading term
`v(x) = 2 √r Σ_j cos (2π (x_j - s_j))` (first-shell coordinates `z_j = √r e^{-2π i s_j}`),
the quadratic slaving term `w_2(v) = ½ (D - Id)^{-1} P_{K^⊥}(v²)` satisfies, at `x = t + s`,
`w_2 = r/(2^d - 1) Σ_j cos (4π t_j) + 4 r/(2^{d/2} - 1) Σ_{i<j} cos (2π t_i) cos (2π t_j)`. -/
theorem cosine_correction_display {d : ℕ} (hd : 11 ≤ d) {r : ℝ} (hr : 0 ≤ r)
    (s t : Fin d → ℝ) :
    ((quadraticCorrection hd (leadingCoordinates r s) : complement d) : Space d)
        (cosLift (fun j => t j + s j)) =
      r / ((2 : ℝ) ^ d - 1) * ∑ j, Real.cos (4 * Real.pi * t j) +
      4 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) *
        ∑ i, ∑ j ∈ Finset.Ioi i, Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j) := by
  rw [quadraticCorrection_apply]
  simp only [term_eval hr]
  have hsplit : ∀ i j : Fin d, (if i = j then r / ((2 : ℝ) ^ d - 1) * Real.cos (4 * Real.pi * t i)
      else 2 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) *
        (Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j))) =
      (if i = j then r / ((2 : ℝ) ^ d - 1) * Real.cos (4 * Real.pi * t i) else 0) +
      (2 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) *
        (if i = j then 0 else Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j)) := by
    intro i j
    by_cases h : i = j <;> simp [h]
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [offDiag_sum_eq (fun i j => Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j))
    (fun i j => mul_comm _ _)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum]
  ring


/-- Surjectivity of `cosLift`. -/
theorem exists_cosLift {d : ℕ} (x : Torus d) : ∃ t : Fin d → ℝ, cosLift t = x := by
  choose t ht using fun j => QuotientAddGroup.mk_surjective (x j)
  exact ⟨t, funext fun j => ht j⟩

theorem cosLift_add {d : ℕ} (t s : Fin d → ℝ) : cosLift (fun j => t j + s j) = cosLift t + cosLift s := by
  funext j
  simp [cosLift]

/-- Leading first-shell coordinates `z_j = √r e^{-2π i x_{0,j}}` for a base point `x₀` of the
torus, so that `assembly d z (x + x₀) = 2 √r Σ_j cos (2π x_j)`. -/
def leadingCoordinatesT {d : ℕ} (r : ℝ) (x₀ : Torus d) : Coordinates d :=
  fun j => (Real.sqrt r : ℂ) * conj (fourier 1 (x₀ j))

theorem leadingCoordinatesT_lift {d : ℕ} (r : ℝ) (s : Fin d → ℝ) :
    leadingCoordinatesT r (cosLift s) = leadingCoordinates r s := by
  funext j
  unfold leadingCoordinatesT leadingCoordinates cosLift
  have h : conj (((2 * Real.pi * s j : ℝ) : ℂ) * Complex.I) =
      (-(2 * Real.pi * s j : ℝ) : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [fourier_one_lift, ← Complex.exp_conj, h]

/-- The displayed trigonometric polynomial `(5.full-branch-w2)` as a function on the torus,
`cos (2π x_j) = Re e_1(x_j)` and `cos (4π x_j) = Re e_2(x_j)`. -/
def displayW2 {d : ℕ} (r : ℝ) (x : Torus d) : ℝ :=
  r / ((2 : ℝ) ^ d - 1) * ∑ j, (fourier 2 (x j)).re +
    4 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) *
      ∑ i, ∑ j ∈ Finset.Ioi i, (fourier 1 (x i)).re * (fourier 1 (x j)).re

theorem fourier_re_lift (n : ℤ) (t : ℝ) :
    (fourier n ((t : ℝ) : UnitAddCircle)).re = Real.cos (2 * Real.pi * n * t) := by
  rw [fourier_coe_apply]
  have : (2 * (Real.pi : ℂ) * Complex.I * n * t / ((1 : ℝ) : ℂ)) = ((2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem displayW2_lift {d : ℕ} (r : ℝ) (t : Fin d → ℝ) :
    displayW2 r (cosLift t) =
      r / ((2 : ℝ) ^ d - 1) * ∑ j, Real.cos (4 * Real.pi * t j) +
      4 * r / ((2 : ℝ) ^ ((d : ℝ) / 2) - 1) *
        ∑ i, ∑ j ∈ Finset.Ioi i, Real.cos (2 * Real.pi * t i) * Real.cos (2 * Real.pi * t j) := by
  unfold displayW2 cosLift
  simp only [fourier_re_lift]
  congr 3
  · funext j; congr 1; push_cast; ring
  · funext i; congr 1; funext j; push_cast; ring_nf

/-- **`(5.full-branch-w2)` on the torus.**  For `r ≥ 0` and a base point `x₀`, the quadratic slaving
term evaluated at the leading first-shell term `v = 2 √r Σ_j cos (2π (x_j - x_{0,j}))` satisfies
`w_2 (x + x₀) = displayW2 r x` for every `x`. -/
theorem cosine_correction_torus {d : ℕ} (hd : 11 ≤ d) {r : ℝ} (hr : 0 ≤ r) (x₀ x : Torus d) :
    ((quadraticCorrection hd (leadingCoordinatesT r x₀) : complement d) : Space d) (x + x₀) =
      displayW2 r x := by
  obtain ⟨s, rfl⟩ := exists_cosLift x₀
  obtain ⟨t, rfl⟩ := exists_cosLift x
  rw [← cosLift_add, leadingCoordinatesT_lift, cosine_correction_display hd hr, displayW2_lift]

/-- The leading term itself: `v (x + x₀) = 2 √r Σ_j cos (2π x_j)`. -/
theorem leading_term_torus {d : ℕ} {r : ℝ} (x₀ x : Torus d) :
    (assembly d (leadingCoordinatesT r x₀) : Space d) (x + x₀) =
      2 * Real.sqrt r * ∑ j, (fourier 1 (x j)).re := by
  obtain ⟨s, rfl⟩ := exists_cosLift x₀
  obtain ⟨t, rfl⟩ := exists_cosLift x
  rw [← cosLift_add, leadingCoordinatesT_lift, assembly_leading_apply]
  simp only [cosLift, fourier_re_lift]
  congr 2
  funext j; congr 1; push_cast; ring

/-- **The manuscript display `(eq:section5-full-branch-w2)` with `r = δ/κ_d`**:
`w_2(x + x₀) = (δ/κ_d) [ Σ_j cos (4π x_j)/(2^d - 1) + 4 Σ_{i<j} cos (2π x_i) cos (2π x_j)/(2^{d/2} - 1) ]`,
for the quadratic slaving term at the leading amplitude `2 √(δ/κ_d)`. -/
theorem cosine_correction_kappa {d : ℕ} (hd : 11 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ) (x₀ x : Torus d) :
    ((quadraticCorrection hd (leadingCoordinatesT (δ / kappa d) x₀) : complement d) : Space d)
        (x + x₀) =
      δ / kappa d * ((∑ j, (fourier 2 (x j)).re) / ((2 : ℝ) ^ d - 1) +
        4 * (∑ i, ∑ j ∈ Finset.Ioi i, (fourier 1 (x i)).re * (fourier 1 (x j)).re) /
          ((2 : ℝ) ^ ((d : ℝ) / 2) - 1)) := by
  have hk : 0 < kappa d := LocalQuartic.kappa_positive hd
  rw [cosine_correction_torus hd (div_nonneg hδ hk.le), displayW2]
  ring

/-- **Bridge to the analytic complement graph.**  Along the leading direction the actual
implicit-function graph `w(1, τ z₀)` equals `τ² w_2(z₀)` up to `O(τ³)` in every `H^σ`, and
`w_2(z₀)` is the displayed cosine polynomial. -/
theorem graph_correction_matches_display {d : ℕ} (hd : 11 ≤ d) {r : ℝ} (hr : 0 ≤ r)
    (x₀ : Torus d) (σ : ℝ) :
    ((fun τ : ℝ => sobolevNorm σ
        ((sliceCorrection hd (τ • leadingCoordinatesT r x₀) -
          τ ^ 2 • quadraticCorrection hd (leadingCoordinatesT r x₀)).val : Space d)) =O[nhds 0]
        (fun τ => ‖τ‖ ^ 3)) ∧
    ∀ x : Torus d,
      ((quadraticCorrection hd (leadingCoordinatesT r x₀) : complement d) : Space d) (x + x₀) =
        displayW2 r x :=
  ⟨correction_directional_sobolev hd σ _, cosine_correction_torus hd hr x₀⟩


/-- `quadraticCorrection` is the manuscript's `w_2(v) = ½ (D - Id)⁻¹ P_{K^⊥}(v²)`, `v = assembly z`:
`P_{K^⊥}` is `complementMap` (removal of the mean and of the first shell) applied to `v²`, and the
resolvent is the inverse of `Id - G` composed with the Green multiplier `|k|^{-d}` on the complement,
i.e. multiplication by `1/(|k|^d - 1)`. -/
theorem quadraticCorrection_eq_half_resolvent_square {d : ℕ} (hd : 11 ≤ d) (z : Coordinates d) :
    quadraticCorrection hd z =
      (1 / 2 : ℝ) • resolvent hd (complementMap d ((assembly d z) ^ 2)) :=
  quadraticCorrection_eq_resolvent hd z

/-- The multiplier of the resolvent at a complement frequency `k`. -/
theorem resolvent_coefficient_multiplier {d : ℕ} (hd : 11 ≤ d) (f : complement d)
    {k : Frequency d} (hk : ComplementFrequency k) :
    ContinuousFirstShell.coefficient k (resolvent hd f).val =
      ((1 / (frequencyLength k ^ d - 1) : ℝ) : ℂ) * ContinuousFirstShell.coefficient k f.val :=
  resolvent_coefficient hd f hk

#print axioms quadraticCorrection_apply
#print axioms cosine_correction_display
#print axioms cosine_correction_torus
#print axioms cosine_correction_kappa
#print axioms leading_term_torus
#print axioms graph_correction_matches_display
#print axioms quadraticCorrection_eq_half_resolvent_square

end BecknerOnofri.V2.Reaudit.MorseBott
