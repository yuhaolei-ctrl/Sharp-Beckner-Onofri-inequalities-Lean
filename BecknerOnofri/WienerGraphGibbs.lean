import BecknerOnofri.WienerGraphAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Topology
namespace BecknerOnofri.HighDim.WienerGraph

/-- The actual continuous-function projection also preserves algebra operations. -/
def toContinuousAlgHom (d m : ℕ) : graph d m →ₐ[ℝ] ContinuousGibbs.Space d where
  toFun := toContinuous d m
  map_zero' := map_zero _
  map_one' := toContinuous_one d m
  map_add' := map_add _
  map_mul' := toContinuous_mul
  commutes' c := by
    change toContinuous d m (c • (1 : graph d m))=algebraMap ℝ (ContinuousGibbs.Space d) c
    rw [map_smul,toContinuous_one,Algebra.smul_def,mul_one]

namespace Gibbs

def mean (d m : ℕ) : graph d m →L[ℝ] ℝ := (ContinuousGibbs.mean d).comp (toContinuous d m)
def exponential {d m : ℕ} (u : graph d m) : graph d m := NormedSpace.exp u
def partition {d m : ℕ} (u : graph d m) : ℝ := mean d m (exponential u)
def normalized {d m : ℕ} (u : graph d m) : graph d m := (partition u)⁻¹ • exponential u

def center (d m : ℕ) : graph d m →L[ℝ] graph d m :=
  ContinuousLinearMap.id ℝ (graph d m)-(mean d m).smulRight 1

def nonlinearRemainder {d m : ℕ} (u : graph d m) : graph d m := normalized u-1-center d m u

@[simp] lemma toContinuous_exponential {d m : ℕ} (u : graph d m) :
    toContinuous d m (exponential u)=ContinuousGibbs.exponential (toContinuous d m u) :=
  NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (toContinuousAlgHom d m) (toContinuous d m).continuous u
    ((NormedSpace.expSeries_radius_eq_top ℝ (graph d m)).symm ▸ edist_lt_top _ _)

@[simp] lemma partition_eq {d m : ℕ} (u : graph d m) :
    partition u=ContinuousGibbs.partition (toContinuous d m u) := by
  simp only [partition,mean,ContinuousLinearMap.comp_apply,toContinuous_exponential,
    ContinuousGibbs.partition]

lemma partition_pos {d m : ℕ} (u : graph d m) : 0<partition u := by
  rw [partition_eq]
  exact ContinuousGibbs.partition_pos _

@[simp] lemma toContinuous_normalized {d m : ℕ} (u : graph d m) :
    toContinuous d m (normalized u)=ContinuousGibbs.normalized (toContinuous d m u) := by
  rw [normalized,map_smul,toContinuous_exponential,partition_eq]
  rfl

@[simp] lemma toContinuous_center {d m : ℕ} (u : graph d m) :
    toContinuous d m (center d m u)=ContinuousGibbs.center d (toContinuous d m u) := by
  change toContinuous d m (u-mean d m u • 1)=_
  rw [map_sub,map_smul,toContinuous_one]
  ext x
  simp only [ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,
    smul_eq_mul,mul_one,ContinuousGibbs.center_apply]
  rfl

@[simp] lemma toContinuous_remainder {d m : ℕ} (u : graph d m) :
    toContinuous d m (nonlinearRemainder u)=ContinuousGibbs.nonlinearRemainder (toContinuous d m u) := by
  simp only [nonlinearRemainder,map_sub,toContinuous_normalized,toContinuous_one,
    toContinuous_center,ContinuousGibbs.nonlinearRemainder]

lemma exponential_analytic {d m : ℕ} (u : graph d m) : AnalyticAt ℝ exponential u :=
  NormedSpace.exp_analytic u
lemma partition_analytic {d m : ℕ} (u : graph d m) : AnalyticAt ℝ partition u :=
  ((mean d m).analyticAt (exponential u)).comp (exponential_analytic u)
lemma normalized_analytic {d m : ℕ} (u : graph d m) : AnalyticAt ℝ normalized u :=
  ((partition_analytic u).inv (partition_pos u).ne').smul (exponential_analytic u)
lemma remainder_analytic {d m : ℕ} (u : graph d m) : AnalyticAt ℝ nonlinearRemainder u :=
  ((normalized_analytic u).sub analyticAt_const).sub ((center d m).analyticAt u)

@[simp] lemma mean_one (d m : ℕ) : mean d m 1=1 := by
  change ContinuousGibbs.mean d (toContinuous d m 1)=1
  rw [toContinuous_one,ContinuousGibbs.mean_one]
@[simp] lemma exponential_zero (d m : ℕ) : exponential (0 : graph d m)=1 := NormedSpace.exp_zero
@[simp] lemma partition_zero (d m : ℕ) : partition (0 : graph d m)=1 := by simp [partition]
@[simp] lemma normalized_zero (d m : ℕ) : normalized (0 : graph d m)=1 := by simp [normalized]
@[simp] lemma remainder_zero (d m : ℕ) : nonlinearRemainder (0 : graph d m)=0 := by
  simp [nonlinearRemainder]

lemma hasFDerivAt_partition_zero (d m : ℕ) :
    HasFDerivAt partition (mean d m) (0 : graph d m) := by
  have he : HasFDerivAt exponential (1 : graph d m →L[ℝ] graph d m) 0 := hasFDerivAt_exp_zero
  convert! (mean d m).hasFDerivAt.comp 0 he using 1

lemma hasFDerivAt_normalized_zero (d m : ℕ) :
    HasFDerivAt normalized (center d m) (0 : graph d m) := by
  have he : HasFDerivAt exponential (1 : graph d m →L[ℝ] graph d m) 0 := hasFDerivAt_exp_zero
  have hi := (hasDerivAt_inv (by simp : partition (0 : graph d m)≠0)).comp_hasFDerivAt
    (0 : graph d m) (hasFDerivAt_partition_zero d m)
  convert! hi.smul he using 1
  apply ContinuousLinearMap.ext
  intro u
  simp [center,exponential_zero,partition_zero,ContinuousLinearMap.smulRight_apply,sub_eq_add_neg]

lemma hasFDerivAt_remainder_zero (d m : ℕ) :
    HasFDerivAt (𝕜 := ℝ) nonlinearRemainder 0 (0 : graph d m) := by
  convert! ((hasFDerivAt_normalized_zero d m).sub_const (1 : graph d m)).sub
    ((center d m).hasFDerivAt (x := (0 : graph d m))) using 1
  simp

#print axioms remainder_analytic
#print axioms hasFDerivAt_remainder_zero
end Gibbs
end BecknerOnofri.HighDim.WienerGraph
