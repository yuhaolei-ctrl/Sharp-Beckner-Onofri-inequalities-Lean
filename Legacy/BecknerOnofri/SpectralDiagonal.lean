import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

/-! Actual bounded real diagonal multipliers in a genuine Hilbert basis. -/
noncomputable section
open scoped Topology BigOperators ENNReal
namespace Legacy.BecknerOnofri.SpectralHeatInverse
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
abbrev Symbol (ι : Type*) := lp (fun _ : ι => ℝ) ∞
abbrev Coordinates (ι : Type*) := lp (fun _ : ι => ℝ) 2

/-- A bounded scalar symbol, with the displayed coordinate function. -/
def boundedSymbol (a : ι → ℝ) (M : ℝ) (ha : ∀ i, ‖a i‖ ≤ M) : Symbol ι :=
  ⟨a,memℓp_infty ⟨M,by rintro _ ⟨i,rfl⟩; exact ha i⟩⟩

private theorem multiply_mem (a : Symbol ι) (x : Coordinates ι) :
    Memℓp (fun i => a i*x i) 2 := by
  apply ((lp.memℓp x).norm.const_mul ‖a‖).mono
  intro i
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero a i) (norm_nonneg _)

def multiply (a : Symbol ι) (x : Coordinates ι) : Coordinates ι :=
  ⟨fun i => a i*x i,multiply_mem a x⟩

private theorem multiply_norm_le (a : Symbol ι) (x : Coordinates ι) :
    ‖multiply a x‖ ≤ ‖a‖*‖x‖ := by
  have h : ‖multiply a x‖ ≤ ‖‖a‖ • x‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro i
    change ‖a i*x i‖ ≤ ‖‖a‖ • x i‖
    rw [norm_mul,norm_smul,Real.norm_of_nonneg (norm_nonneg a)]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero a i) (norm_nonneg _)
  simpa only [norm_smul,Real.norm_of_nonneg (norm_nonneg a)] using h

def lpMultiplier (a : Symbol ι) : Coordinates ι →L[ℝ] Coordinates ι :=
  LinearMap.mkContinuous
    { toFun := multiply a
      map_add' := by intro x y; ext i; change a i*(x i+y i)=a i*x i+a i*y i; ring
      map_smul' := by intro c x; ext i; change a i*(c*x i)=c*(a i*x i); ring }
    ‖a‖ (multiply_norm_le a)

/-- Conjugate actual sequence multiplication by the Hilbert basis isometry. -/
def diagonal (e : HilbertBasis ι ℝ H) (a : Symbol ι) : H →L[ℝ] H :=
  e.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lpMultiplier a).comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem repr_diagonal (e : HilbertBasis ι ℝ H) (a : Symbol ι) (u : H) (i : ι) :
    e.repr (diagonal e a u) i = a i*e.repr u i := by
  change e.repr (e.repr.symm (multiply a (e.repr u))) i = _
  rw [e.repr.apply_symm_apply]
  rfl

/-- Every uniform coefficient bound gives the corresponding actual operator norm estimate. -/
theorem diagonal_apply_norm_le (e : HilbertBasis ι ℝ H) (a : Symbol ι)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) (u : H) :
    ‖diagonal e a u‖ ≤ M*‖u‖ := by
  have h : ‖e.repr (diagonal e a u)‖ ≤ ‖M • e.repr u‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro i
    rw [repr_diagonal]
    change ‖a i*e.repr u i‖ ≤ ‖M • e.repr u i‖
    rw [norm_mul,norm_smul,Real.norm_of_nonneg hM]
    exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
  simpa only [e.repr.norm_map,norm_smul,Real.norm_of_nonneg hM] using h

theorem diagonal_norm_le (e : HilbertBasis ι ℝ H) (a : Symbol ι)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ i, ‖a i‖ ≤ M) : ‖diagonal e a‖ ≤ M :=
  (diagonal e a).opNorm_le_bound hM (diagonal_apply_norm_le e a hM ha)

theorem diagonal_sub (e : HilbertBasis ι ℝ H) (a b : Symbol ι) :
    diagonal e (a-b) = diagonal e a-diagonal e b := by
  ext u
  apply e.repr.injective
  ext i
  simp only [ContinuousLinearMap.sub_apply,map_sub,lp.coeFn_sub,Pi.sub_apply,repr_diagonal]
  change (a i-b i)*e.repr u i=a i*e.repr u i-b i*e.repr u i
  ring

theorem diagonal_symmetric (e : HilbertBasis ι ℝ H) (a : Symbol ι) :
    (diagonal e a).IsSymmetric := by
  intro u v
  change inner ℝ (diagonal e a u) v = inner ℝ u (diagonal e a v)
  rw [← e.repr.inner_map_map (diagonal e a u) v,
    ← e.repr.inner_map_map u (diagonal e a v),lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [repr_diagonal,RCLike.inner_apply,conj_trivial]
  ring

def coordinate (e : HilbertBasis ι ℝ H) (i : ι) : H →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : ι => ℝ) 2 i).comp e.repr.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem coordinate_apply (e : HilbertBasis ι ℝ H) (i : ι) (u : H) :
    coordinate e i u = e.repr u i := rfl

theorem ext_coordinates (e : HilbertBasis ι ℝ H) {u v : H}
    (h : ∀ i, coordinate e i u = coordinate e i v) : u = v := by
  apply e.repr.injective
  exact lp.ext (funext h)

#print axioms diagonal_symmetric
#print axioms diagonal_norm_le
end Legacy.BecknerOnofri.SpectralHeatInverse
