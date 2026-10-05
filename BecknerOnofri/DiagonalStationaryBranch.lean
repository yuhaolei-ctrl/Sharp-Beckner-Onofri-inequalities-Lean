module

public import BecknerOnofri.DiagonalScalarBranch
public import BecknerOnofri.GraphRegularity
public import BecknerOnofri.Kappa
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Actual smooth full Euler solutions on the supercritical side, obtained
from the analytic symmetric branch by the intermediate value theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics Set
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ContinuousComplement ReducedCubicExpansion

/-- The actual torus potential on the analytic scalar branch. -/
def branchPotential {d : ℕ} (hd : 12 ≤ d) (t : ℝ) : Space d :=
  ReducedEquation.potential hd (parameter hd t,realDiagonal d t)

theorem branch_coordinates_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (fun t : ℝ => (parameter hd t,realDiagonal d t)) (𝓝 0)
      (𝓝 (1,(0 : Coordinates d))) := by
  exact (RealDiagonalReduction.diagonalEmbedding_tendsto d).comp (parameter_pair_tendsto hd)

theorem branchPotential_analytic {d : ℕ} (hd : 12 ≤ d) :
    AnalyticAt ℝ (branchPotential hd) 0 := by
  have hi : AnalyticAt ℝ (fun t : ℝ => (parameter hd t,realDiagonal d t)) 0 :=
    (parameter_analytic hd).prod ((realDiagonal d).analyticAt 0)
  have ho : AnalyticAt ℝ (ReducedEquation.potential hd)
      (parameter hd 0,realDiagonal d 0) := by
    simpa only [parameter_base,map_zero] using ReducedEquation.potential_analytic hd
  exact ho.comp (f := fun t : ℝ => (parameter hd t,realDiagonal d t)) hi

@[simp] theorem branchPotential_base {d : ℕ} (hd : 12 ≤ d) : branchPotential hd 0 = 0 := by
  simp [branchPotential,ReducedEquation.potential,GreenLocalBranch.correction_base]

@[simp] theorem branchPotential_mean {d : ℕ} (hd : 12 ≤ d) (t : ℝ) :
    mean d (branchPotential hd t) = 0 := mean_reconstruction _

@[simp] theorem branchPotential_coordinates {d : ℕ} (hd : 12 ≤ d) (t : ℝ) :
    coordinates d (branchPotential hd t) = realDiagonal d t := by
  simp only [branchPotential,ReducedEquation.potential,reconstruction_apply,map_add,
    coordinates_assembly,ReducedEquation.coordinates_complement,add_zero]

theorem branchPotential_nonzero {d : ℕ} (hd : 12 ≤ d) {t : ℝ} (ht : t ≠ 0) :
    branchPotential hd t ≠ 0 := by
  intro h
  have hc := congrArg (fun u : Space d => coordinates d u (RealDiagonalReduction.firstIndex hd)) h
  apply ht
  simpa only [branchPotential_coordinates,realDiagonal_apply,map_zero,Pi.zero_apply,
    Complex.ofReal_eq_zero] using hc

theorem branchPotential_regular {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), SmoothOnTorus (branchPotential hd t) ∧
      ∀ s : ℝ, InSobolev s (branchPotential hd t) :=
  (branch_coordinates_tendsto hd).eventually (GraphRegularity.potential_regular hd)

theorem branchPotential_full_zero {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), ReducedEquation.full d (parameter hd t) (branchPotential hd t) = 0 := by
  filter_upwards [(branch_coordinates_tendsto hd).eventually (ReducedEquation.graph_full_iff_reduced hd),
    parameter_reduced_zero hd] with t hf hr
  exact hf.mpr hr

/-- The scalar branch lies on the strict supercritical side away from zero. -/
theorem parameter_lower_bound {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), kappa d / 2 * t^2 ≤ parameter hd t-1 := by
  obtain ⟨C,hC⟩ := (parameter_expansion hd).exists_pos
  have hlim : Tendsto (fun t : ℝ => C*‖t‖^2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => C*‖t‖^2) := continuous_const.mul (continuous_norm.pow 2)
    simpa using hc.continuousAt.tendsto (x := (0:ℝ))
  have hk : 0 < kappa d/2 := by have := kappa_pos d hd; positivity
  filter_upwards [hC.2.bound,hlim.eventually (gt_mem_nhds hk)] with t hb ht
  simp only [Real.norm_eq_abs,abs_pow,abs_abs] at hb ht
  have hfour : |t|^4 = t^4 := by
    calc
      _ = (|t|^2)^2 := by ring
      _ = (t^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  rw [sq_abs] at ht
  rw [hfour] at hb
  have hh := (abs_le.mp hb).1
  nlinarith [mul_le_mul_of_nonneg_right (le_of_lt ht) (sq_nonneg t)]

/-- Every sufficiently small supercritical parameter has a positive-amplitude,
nonzero, mean-zero smooth solution of the actual full Euler equation. -/
theorem exists_stationary_for_every_parameter {d : ℕ} (hd : 12 ≤ d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 1 < μ → μ < 1+ε →
      ∃ t : ℝ, 0 < t ∧ parameter hd t = μ ∧
        branchPotential hd t ≠ 0 ∧ mean d (branchPotential hd t) = 0 ∧
        SmoothOnTorus (branchPotential hd t) ∧
        (∀ s : ℝ, InSobolev s (branchPotential hd t)) ∧
        ReducedEquation.full d μ (branchPotential hd t) = 0 := by
  have hall : ∀ᶠ t in 𝓝 (0:ℝ),
      ContinuousAt (parameter hd) t ∧ (kappa d/2*t^2 ≤ parameter hd t-1) ∧
      (SmoothOnTorus (branchPotential hd t) ∧ ∀ s : ℝ, InSobolev s (branchPotential hd t)) ∧
      ReducedEquation.full d (parameter hd t) (branchPotential hd t) = 0 := by
    filter_upwards [(parameter_analytic hd).eventually_analyticAt,parameter_lower_bound hd,
      branchPotential_regular hd,branchPotential_full_zero hd] with t ha hb hc hd'
    exact ⟨ha.continuousAt,hb,hc,hd'⟩
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hall
  let a : ℝ := r/2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith
  have hinterval (t : ℝ) (ht : t ∈ Icc 0 a) : dist t 0 < r := by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact ht.2.trans_lt har
  have haa := hball (hinterval a ⟨ha.le,le_rfl⟩)
  have hμa : 1 < parameter hd a := by
    have hk := kappa_pos d hd
    have hp : 0 < kappa d/2*a^2 := by positivity
    linarith [haa.2.1]
  refine ⟨parameter hd a-1,by linarith,?_⟩
  intro μ hμ hμε
  have hc : ContinuousOn (parameter hd) (Icc 0 a) := fun t ht =>
    (hball (hinterval t ht)).1.continuousWithinAt
  have him : μ ∈ Icc (parameter hd 0) (parameter hd a) := by
    rw [parameter_base]
    constructor <;> linarith
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc ha.le hc him
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro hz
    have hbad : μ = 1 := by simpa only [← hz,parameter_base] using he.symm
    linarith
  have hprops := hball (hinterval t ht)
  refine ⟨t,ht0,he,branchPotential_nonzero hd ht0.ne',branchPotential_mean hd t,
    hprops.2.2.1.1,hprops.2.2.1.2,?_⟩
  simpa only [he] using hprops.2.2.2

#print axioms branchPotential_full_zero
#print axioms exists_stationary_for_every_parameter
end BecknerOnofri.HighDim.DiagonalScalarBranch
