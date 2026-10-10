module

public import BecknerOnofri.V2.Reaudit.HeatKernel.RadialJet

@[expose] public section

/-! # S014: multinomial expansion of the radial jet at the origin

`((radialD y)^[n] f)(0) / n! = ∑_{|α| = n} (∂^α f(0) / α!) y^α`, the repository's
`mixedPartial (directions α) f 0` playing the role of `∂^α f(0)`.

The proof introduces the linear functional `Lam f` on `MvPolynomial (Fin d) ℝ` with
`Lam f (X^α) = ∂^α f(0)`.  It satisfies `Lam (∂_i f) p = Lam f (X_i * p)` by the order
independence of mixed partials on the cube (`mixedPartial_eq_of_directionIndex_eq`), hence
`((radialD y)^[n] f)(0) = Lam f ((∑ y_i X_i)^n)`; the multinomial theorem finishes.
-/

noncomputable section
open Set Finset
open scoped ContDiff
namespace BecknerOnofri.V2.Reaudit.HeatKernel
open Legacy.BecknerOnofri.FiniteDifferences

variable {d : ℕ}

/-- `∂^α f (0)`, with the repository's fixed ordering of the directions of `α`. -/
def jetAt0 (f : Space d → ℝ) (a : Index d) : ℝ := mixedPartial (directions a) f 0

/-- The Taylor coefficient `∂^α f(0)/α!`. -/
def taylorCoeff (f : Space d → ℝ) (a : Index d) : ℝ :=
  jetAt0 f a / (∏ i, ((a i).factorial : ℝ))

/-- The functional `X^α ↦ ∂^α f(0)`, on a polynomial `∑ c_α X^α` it is `∑ c_α ∂^α f(0)`. -/
def LamFun (f : Space d → ℝ) (p : MvPolynomial (Fin d) ℝ) : ℝ :=
  ∑ a ∈ p.support, p.coeff a * jetAt0 f a

theorem LamFun_eq_of_superset (f : Space d → ℝ) {p : MvPolynomial (Fin d) ℝ} {S : Finset (Index d)}
    (h : p.support ⊆ S) : LamFun f p = ∑ a ∈ S, p.coeff a * jetAt0 f a := by
  unfold LamFun
  apply Finset.sum_subset h
  intro a _ ha
  have : p.coeff a = 0 := by
    by_contra hc
    exact ha (MvPolynomial.mem_support_iff.mpr hc)
  simp [this]

/-- The linear functional `X^α ↦ ∂^α f(0)`. -/
def Lam (f : Space d → ℝ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ where
  toFun := LamFun f
  map_add' p q := by
    classical
    have h1 : (p + q).support ⊆ p.support ∪ q.support := MvPolynomial.support_add
    rw [LamFun_eq_of_superset f h1, LamFun_eq_of_superset f (Finset.subset_union_left (s₂ := q.support)),
      LamFun_eq_of_superset f (Finset.subset_union_right (s₁ := p.support)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [MvPolynomial.coeff_add]; ring
  map_smul' c p := by
    have h1 : (c • p).support ⊆ p.support := MvPolynomial.support_smul
    rw [RingHom.id_apply, LamFun_eq_of_superset f h1]
    unfold LamFun
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul]; ring

theorem Lam_apply (f : Space d → ℝ) (p : MvPolynomial (Fin d) ℝ) :
    Lam f p = ∑ a ∈ p.support, p.coeff a * jetAt0 f a := rfl

theorem Lam_monomial (f : Space d → ℝ) (a : Index d) (c : ℝ) :
    Lam f (MvPolynomial.monomial a c) = c * jetAt0 f a := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  rw [Lam_apply, MvPolynomial.support_monomial, if_neg hc]
  simp [MvPolynomial.coeff_monomial]

theorem zero_mem_closedCube (d : ℕ) : (0 : Space d) ∈ closedCube d := by
  simp [closedCube]

theorem directions_zero : directions (0 : Index d) = [] := by
  simp [directions]

theorem Lam_one (f : Space d → ℝ) : Lam f 1 = f 0 := by
  have : (1 : MvPolynomial (Fin d) ℝ) = MvPolynomial.monomial 0 1 := rfl
  rw [this, Lam_monomial, one_mul]
  simp [jetAt0, directions_zero]

theorem jetAt0_coordinateDerivative {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (i : Fin d) (a : Index d) :
    jetAt0 (coordinateDerivative i f) a = jetAt0 f (a + Finsupp.single i 1) := by
  unfold jetAt0
  have h1 : mixedPartial (directions a) (coordinateDerivative i f) 0 =
      mixedPartial (i :: directions a) f 0 := rfl
  rw [h1]
  apply mixedPartial_eq_of_directionIndex_eq _ hf (zero_mem_closedCube d)
  rw [directionIndex_cons, directionIndex_directions, directionIndex_directions]

theorem Lam_coordinateDerivative {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (i : Fin d) (p : MvPolynomial (Fin d) ℝ) :
    Lam (coordinateDerivative i f) p = Lam f (MvPolynomial.X i * p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [Lam_monomial, jetAt0_coordinateDerivative hf, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
      Lam_monomial, one_mul, add_comm]
  | add p q hp hq => rw [map_add, mul_add, map_add, hp, hq]

theorem Lam_radialD {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d)) (y : Space d)
    (p : MvPolynomial (Fin d) ℝ) :
    Lam (radialD y f) p = ∑ i, y i * Lam f (MvPolynomial.X i * p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have h1 : jetAt0 (radialD y f) u = ∑ i, y i * jetAt0 (coordinateDerivative i f) u := by
      unfold jetAt0
      exact mixedPartial_sum (directions u) Finset.univ y (fun i => coordinateDerivative i f)
        (fun i => contDiffOn_coordinateDerivative hf i) (zero_mem_closedCube d)
    rw [Lam_monomial, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Lam_coordinateDerivative hf, Lam_monomial]
    ring
  | add p q hp hq =>
    rw [map_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, map_add, mul_add]

/-- The radial jet at the origin is the functional `Lam f` applied to a power of `∑ y_i X_i`. -/
theorem radialD_iterate_zero_eq_Lam {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (y : Space d) (n : ℕ) :
    ((radialD y)^[n] f) 0 = Lam f ((∑ i, y i • (MvPolynomial.X i : MvPolynomial (Fin d) ℝ)) ^ n) := by
  induction n generalizing f with
  | zero => simp [Lam_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (contDiffOn_radialD y hf), Lam_radialD hf]
    rw [pow_succ', Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_mul_assoc, map_smul, smul_eq_mul]

/-- Degree of a multi-index. -/
def deg (a : Index d) : ℕ := ∑ i, a i

theorem multinomial_mul_factorial (a : Index d) :
    ((a.multinomial : ℕ) : ℝ) * (∏ i, ((a i).factorial : ℝ)) = ((deg a).factorial : ℝ) := by
  have h := Nat.multinomial_spec a.support a
  have e1 : ∏ i ∈ a.support, (a i).factorial = ∏ i, (a i).factorial := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi]
    simp
  have e2 : ∑ i ∈ a.support, a i = deg a := by
    unfold deg
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    exact Finsupp.notMem_support_iff.mp hi
  rw [e1, e2] at h
  rw [Finsupp.multinomial_eq]
  exact_mod_cast (by rw [mul_comm]; exact h : (Nat.multinomial a.support a) * (∏ i, (a i).factorial) = (deg a).factorial)

/-- The `n`-th homogeneous piece of the Taylor series along the ray. -/
def taylorTerm (y : Space d) (f : Space d → ℝ) (a : Index d) : ℝ :=
  taylorCoeff f a * ∏ i, y i ^ a i

/-- **Multinomial expansion of the radial jet**: `((radialD y)^[n] f)(0)/n!` is the sum of the
Taylor terms of degree `n`, as an (essentially finite) `HasSum` over all multi-indices. -/
theorem hasSum_radial_jet_degree {f : Space d → ℝ} (hf : ContDiffOn ℝ ∞ f (closedCube d))
    (y : Space d) (n : ℕ) :
    HasSum (fun a : Index d => if deg a = n then taylorTerm y f a else 0)
      (((radialD y)^[n] f) 0 / (n.factorial : ℝ)) := by
  classical
  set P : MvPolynomial (Fin d) ℝ := (∑ i, y i • (MvPolynomial.X i : MvPolynomial (Fin d) ℝ)) ^ n
    with hP
  have hcoeff : ∀ a : Index d, P.coeff a =
      if deg a = n then (a.multinomial : ℝ) * ∏ i, y i ^ a i else 0 := by
    intro a
    have := MvPolynomial.coeff_linearCombination_X_pow_of_fintype y a n
    rw [hP, this]
    have hs : a.sum (fun _ m => m) = deg a := by
      unfold deg
      exact Finsupp.sum_fintype a (fun _ m => m) (fun _ => rfl)
    have hp : a.prod (fun r m => y r ^ m) = ∏ i, y i ^ a i :=
      Finsupp.prod_fintype a _ (fun _ => pow_zero _)
    rw [hs, hp]
  have hLam : ((radialD y)^[n] f) 0 = ∑ a ∈ P.support, P.coeff a * jetAt0 f a := by
    rw [radialD_iterate_zero_eq_Lam hf y n]
    rfl
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by positivity
  have hterm : ∀ a : Index d, (if deg a = n then taylorTerm y f a else 0) =
      P.coeff a * jetAt0 f a / (n.factorial : ℝ) := by
    intro a
    rw [hcoeff a]
    by_cases hd : deg a = n
    · simp only [hd, if_true]
      unfold taylorTerm taylorCoeff
      have hm := multinomial_mul_factorial a
      rw [hd] at hm
      have hpos : (0 : ℝ) < ∏ i, ((a i).factorial : ℝ) := by
        apply Finset.prod_pos; intro i _; positivity
      have hmult : ((a.multinomial : ℕ) : ℝ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hm
        exact (ne_of_gt hfact) hm.symm
      rw [← hm]
      field_simp
    · simp [hd]
  have hsum : HasSum (fun a : Index d => P.coeff a * jetAt0 f a / (n.factorial : ℝ))
      (((radialD y)^[n] f) 0 / (n.factorial : ℝ)) := by
    rw [hLam, Finset.sum_div]
    apply hasSum_sum_of_ne_finset_zero
    intro a ha
    have : P.coeff a = 0 := by
      by_contra h
      exact ha (MvPolynomial.mem_support_iff.mpr h)
    simp [this]
  simpa only [hterm] using hsum

end BecknerOnofri.V2.Reaudit.HeatKernel
