module

public import BecknerOnofri.Paper2.PeriodizationDefinitions
public import BecknerOnofri.ElevenPeriodizedContinuity
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section

/-! Locally uniform convergence of every coordinate derivative of the literal
Euclidean periodization. Derivatives are ordinary derivatives along coordinate
lines, over the whole Euclidean space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Paper2.Periodization
open HighDim HighDim.Eleven

def denominator (x : E) : ℝ := 1 + 25 * ∑ i, (x i)^2
lemma denominator_pos (x : E) : 0 < denominator x := by
  unfold denominator
  positivity
lemma denominator_one (x : E) : 1 ≤ denominator x := by
  have h : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  dsimp [denominator]
  linarith
lemma coord_le_denominator (x : E) (i : Fin 11) : |x i| ≤ denominator x := by
  have h := Finset.single_le_sum (f := fun j : Fin 11 => (x j)^2)
    (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hs := sq_nonneg (|x i| - 1)
  have hs2 := sq_abs (x i)
  dsimp [denominator]
  nlinarith [sq_nonneg (x i)]

lemma line_deriv (x : E) (i j : Fin 11) :
    HasDerivAt (fun t => line x i t j) (if j=i then 1 else 0) 0 := by
  simpa [line, Pi.single_apply, eq_comm] using
    (((hasDerivAt_id (0:ℝ)).mul_const ((Pi.single i (1:ℝ) : E) j)).const_add (x j))

lemma denominator_deriv (x : E) (i : Fin 11) :
    HasDerivAt (fun t => denominator (line x i t)) (50*x i) 0 := by
  have h := ((HasDerivAt.sum (u := Finset.univ) (fun j _ => (line_deriv x i j).pow 2)).const_mul 25).const_add 1
  convert! h using 1 <;> simp [denominator, line, Finset.sum_ite_eq'] <;> ring

inductive Expr where
  | const (a : ℝ)
  | inv
  | ratio (i : Fin 11)
  | add (p q : Expr)
  | mul (p q : Expr)

def Expr.eval : Expr → E → ℝ
  | .const a, _ => a
  | .inv, x => (denominator x)⁻¹
  | .ratio i, x => x i / denominator x
  | .add p q, x => p.eval x + q.eval x
  | .mul p q, x => p.eval x * q.eval x

def Expr.diff (i : Fin 11) : Expr → Expr
  | .const _ => .const 0
  | .inv => .mul (.const (-50)) (.mul (.ratio i) .inv)
  | .ratio j => .add (.mul (.const (if j=i then 1 else 0)) .inv)
      (.mul (.const (-50)) (.mul (.ratio j) (.ratio i)))
  | .add p q => .add (p.diff i) (q.diff i)
  | .mul p q => .add (.mul (p.diff i) q) (.mul p (q.diff i))

lemma Expr.hasDeriv (p : Expr) (x : E) (i : Fin 11) :
    HasDerivAt (fun t => p.eval (line x i t)) ((p.diff i).eval x) 0 := by
  induction p with
  | const a => simpa [Expr.eval, Expr.diff] using hasDerivAt_const (0:ℝ) a
  | inv =>
    convert! (denominator_deriv x i).inv (by simpa [line] using (denominator_pos x).ne') using 1
    simp only [Expr.diff, Expr.eval, line, zero_smul, add_zero]
    field_simp
    <;> ring
  | ratio j =>
    convert! (line_deriv x i j).div (denominator_deriv x i)
      (by simpa [line] using (denominator_pos x).ne') using 1
    simp only [Expr.diff, Expr.eval, line, zero_smul, add_zero]
    split_ifs <;> field_simp <;> ring
  | add p q hp hq => convert! hp.add hq using 1
  | mul p q hp hq =>
    convert! hp.mul hq using 1
    simp [Expr.diff, Expr.eval, line]

lemma Expr.bounded (p : Expr) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |p.eval x| ≤ C := by
  induction p with
  | const a => exact ⟨|a|, abs_nonneg _, fun _ => le_rfl⟩
  | inv =>
    refine ⟨1, by norm_num, fun x => ?_⟩
    simpa [Expr.eval, abs_of_pos (inv_pos.mpr (denominator_pos x))] using
      (inv_le_one₀ (denominator_pos x)).mpr (denominator_one x)
  | ratio i =>
    refine ⟨1, by norm_num, fun x => ?_⟩
    simp only [Expr.eval, abs_div, abs_of_pos (denominator_pos x)]
    exact (div_le_one (denominator_pos x)).mpr (coord_le_denominator x i)
  | add p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    exact ⟨C+D, add_nonneg hC hD, fun x => (abs_add_le _ _).trans (add_le_add (hp x) (hq x))⟩
  | mul p q hp hq =>
    obtain ⟨C,hC,hp⟩ := hp
    obtain ⟨D,hD,hq⟩ := hq
    refine ⟨C*D, mul_nonneg hC hD, fun x => ?_⟩
    rw [Expr.eval, abs_mul]
    exact mul_le_mul (hp x) (hq x) (abs_nonneg _) hC

lemma profile_deriv (x : E) (i : Fin 11) :
    HasDerivAt (fun t => euclideanProfile (line x i t))
      (-550 * (x i / denominator x) * euclideanProfile x) 0 := by
  have h := ((hasDerivAt_zpow (-11) (denominator (line x i 0)) (Or.inl (by
    simpa [line] using (denominator_pos x).ne'))).comp 0 (denominator_deriv x i)).const_mul
      ((5:ℝ)^11 * (122880 / Real.pi^6))
  convert! h using 1
  simp only [line, zero_smul, add_zero, Int.cast_neg, Int.cast_ofNat]
  rw [show (-11:ℤ)-1 = -12 by norm_num]
  change -550 * (x i / denominator x) *
      ((5:ℝ)^11 * (122880 / Real.pi^6) * (denominator x)^(-11:ℤ)) =
        (5:ℝ)^11 * (122880 / Real.pi^6) * ((-11:ℝ) * (denominator x)^(-12:ℤ) * (50*x i))
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  <;> ring

lemma mixed_repr (is : List (Fin 11)) :
    ∃ p : Expr, mixed is euclideanProfile = fun x => p.eval x * euclideanProfile x := by
  induction is with
  | nil => exact ⟨.const 1, by funext x; simp [mixed, Expr.eval]⟩
  | cons i is ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨.add (p.diff i) (.mul p (.mul (.const (-550)) (.ratio i))), ?_⟩
    funext x
    simp only [mixed, hp, coordinatePartial]
    convert! ((p.hasDeriv x i).mul (profile_deriv x i)).deriv using 1
    simp [Expr.eval, line]
    ring

lemma mixed_bound (is : List (Fin 11)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |mixed is euclideanProfile x| ≤ C * euclideanProfile x := by
  obtain ⟨p,hp⟩ := mixed_repr is
  obtain ⟨C,hC,hbound⟩ := p.bounded
  refine ⟨C,hC,fun x => ?_⟩
  rw [hp, abs_mul, abs_of_pos (euclideanProfile_pos x)]
  exact mul_le_mul_of_nonneg_right (hbound x) (euclideanProfile_pos x).le

lemma mixed_translate (is : List (Fin 11)) (f : E → ℝ) (a : E) :
    mixed is (fun x => f (x+a)) = fun x => mixed is f (x+a) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    funext x
    simp only [mixed, ih, coordinatePartial]
    congr 1
    funext t
    congr 1
    ext j
    simp [line, add_assoc, add_comm, add_left_comm]

/-- Every coordinate derivative of every summand is bounded by one summable
majorant on each compact set. The bound applies to the original rational
Euclidean profile, without replacing it by its Fourier expansion. -/
theorem derivative_majorant (is : List (Fin 11)) (K : Set E) (hK : IsCompact K) :
    ∃ b : Frequency 11 → ℝ, Summable b ∧
      ∀ n x, x ∈ K →
        ‖mixed is (fun y => euclideanProfile (fun j => y j+(n j:ℝ))) x‖ ≤ b n := by
  obtain ⟨C,hC,hbound⟩ := mixed_bound is
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0:E)
  let A : ℝ := (5:ℝ)^11 * (122880 / Real.pi^6) * (2+22*R^2)^11
  refine ⟨fun n => C * (A * Legacy.TorusEndpoint.GreenMultiplierSummability.productMajorant n),
    ((Legacy.TorusEndpoint.GreenMultiplierSummability.summable_productMajorant 11).mul_left A).mul_left C,
    fun n x hx => ?_⟩
  have hxR : ∀ i, |x i| ≤ R := by
    intro i
    have hn : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hKR hx
    exact (show |x i| ≤ ‖x‖ by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i).trans hn.le
  have he := congrFun (mixed_translate is euclideanProfile (fun i => (n i:ℝ))) x
  change mixed is (fun y => euclideanProfile (fun j => y j+(n j:ℝ))) x = _ at he
  rw [he, Real.norm_eq_abs]
  exact (hbound _).trans (mul_le_mul_of_nonneg_left
    (translated_profile_majorant x n hR.le hxR) hC)

/-- The series of every ordered coordinate derivative converges locally
uniformly, with finite lattice subsets directed by inclusion. -/
theorem derivatives_locally_uniform (is : List (Fin 11)) :
    TendstoLocallyUniformly
      (fun S : Finset (Frequency 11) => fun x : E =>
        ∑ n ∈ S, mixed is (fun y => euclideanProfile (fun j => y j+(n j:ℝ))) x)
      (fun x : E => ∑' n : Frequency 11,
        mixed is (fun y => euclideanProfile (fun j => y j+(n j:ℝ))) x) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨b,hb,hbound⟩ := derivative_majorant is K hK
  exact tendstoUniformlyOn_tsum hb hbound

#print axioms derivatives_locally_uniform
end BecknerOnofri.Paper2.Periodization
