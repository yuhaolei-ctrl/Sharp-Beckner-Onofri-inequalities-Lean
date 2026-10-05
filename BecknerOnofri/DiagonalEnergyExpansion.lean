import BecknerOnofri.ReducedEnergyJointExpansion
import BecknerOnofri.DiagonalStationaryBranch
import BecknerOnofri.CriticalGraphCoercivity

/-! The manuscript's sharp leading pressure coefficient on the actual
smooth full-coordinate stationary branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ReducedCubicExpansion ReducedQuarticExpansion
open ReducedEnergyGradient UniformComplementBounds

def branchDelta {d : ℕ} (hd : 12 ≤ d) (t : ℝ) : ℝ := 1-1/parameter hd t

def branchEnergy {d : ℕ} (hd : 12 ≤ d) (t : ℝ) : ℝ :=
  (dualFunctional (parameter hd t*spectralThreshold d) (branchPotential hd t)).toReal

theorem parameter_eventually_ne_zero {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ t in 𝓝 (0:ℝ), parameter hd t ≠ 0 := by
  have hc := (parameter_analytic hd).continuousAt
  exact hc.eventually_ne (by rw [parameter_base]; norm_num)

theorem branchDelta_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t : ℝ => branchDelta hd t-kappa d*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
  have hinv : (fun t : ℝ => (parameter hd t)⁻¹) =O[𝓝 0] (fun _ => (1:ℝ)) :=
    ((parameter_analytic hd).inv (by rw [parameter_base]; norm_num)).continuousAt.isBigO
  have hs := ((parameter_quadratic_bound hd).pow 2).mul hinv
  have hs' : (fun t : ℝ => (parameter hd t-1)^2*(parameter hd t)⁻¹)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^4) := by
    convert! hs using 1 <;> (funext t; ring)
  apply ((parameter_expansion hd).sub hs').congr'
  · filter_upwards [parameter_eventually_ne_zero hd] with t ht
    unfold branchDelta
    field_simp
    ring
  · rfl

theorem branchDelta_quadratic {d : ℕ} (hd : 12 ≤ d) :
    branchDelta hd =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
  have herror := (branchDelta_expansion hd).trans
    (norm_pow_bigO_of_le (E := ℝ) (by decide : 2 ≤ 4))
  have hmain : (fun t : ℝ => kappa d*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
    exact (isBigO_refl (fun t : ℝ => t^2) (𝓝 0)).norm_right.congr_right
      (fun t => by simp [norm_pow]) |>.const_mul_left (kappa d)
  apply (herror.add hmain).congr_left
  intro t
  ring

theorem quarticValue_realDiagonal {d : ℕ} (hd : 12 ≤ d) (t : ℝ) :
    quarticValue (realDiagonal d t) = -(d:ℝ)*kappa d/2*t^4 := by
  rw [ReducedPhysicalEnergy.quarticValue_eq_reducedQuartic]
  simp only [realDiagonal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    reducedQuartic, zero_mul, zero_add, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold kappa
  ring

theorem branchEnergy_amplitude_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t : ℝ => branchEnergy hd t-(d:ℝ)*kappa d/2*t^4)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
  have hdiag : (fun t : ℝ => ‖realDiagonal d t‖) =O[𝓝 0] (fun t : ℝ => ‖t‖) :=
    ((realDiagonal d).isBigO_id (𝓝 0)).norm_left.norm_right
  have hδ := (parameter_quadratic_bound hd).norm_left
  simp only [Real.norm_eq_abs] at hδ
  have hright : (fun t : ℝ => ‖realDiagonal d t‖^6 +
      |parameter hd t-1| *‖realDiagonal d t‖^4) =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
    have hm := hδ.mul (hdiag.pow 4)
    have hm' : (fun t : ℝ => |parameter hd t-1| *‖realDiagonal d t‖^4)
        =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
      convert! hm using 1 <;> (funext t; simp only [Real.norm_eq_abs]; ring)
    exact (hdiag.pow 6).add hm'
  have he := ((physicalReducedEnergy_joint_quartic hd).comp_tendsto
    (branch_coordinates_tendsto hd)).trans hright
  have ht : (fun t : ℝ => t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
    exact (isBigO_refl (fun t : ℝ => t^2) (𝓝 0)).norm_right.congr_right
      (fun t => by simp [norm_pow])
  have hdelt : (fun t : ℝ => (d:ℝ)*(branchDelta hd t-kappa d*t^2)*t^2)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
    convert! (((branchDelta_expansion hd).const_mul_left (d:ℝ)).mul ht) using 1
    funext t
    ring
  apply (he.add hdelt).congr_left
  intro t
  dsimp only [Function.comp_apply]
  rw [quarticValue_realDiagonal hd]
  simp only [realDiagonal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change physicalReducedEnergy hd (parameter hd t,realDiagonal d t) -
    (1-1/parameter hd t)*((d:ℝ)*t^2) - (-(d:ℝ)*kappa d/2*t^4) +
      (d:ℝ)*(branchDelta hd t-kappa d*t^2)*t^2 = _
  change branchEnergy hd t - branchDelta hd t*((d:ℝ)*t^2) -
    (-(d:ℝ)*kappa d/2*t^4) + (d:ℝ)*(branchDelta hd t-kappa d*t^2)*t^2 = _
  ring

theorem branchEnergy_delta_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun t : ℝ => branchEnergy hd t-(d:ℝ)/(2*kappa d)*(branchDelta hd t)^2)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
  have ht : (fun t : ℝ => kappa d*t^2) =O[𝓝 0] (fun t : ℝ => ‖t‖^2) := by
    exact (isBigO_refl (fun t : ℝ => t^2) (𝓝 0)).norm_right.congr_right
      (fun t => by simp [norm_pow]) |>.const_mul_left (kappa d)
  have hh : (fun t : ℝ => (branchDelta hd t)^2-(kappa d)^2*t^4)
      =O[𝓝 0] (fun t : ℝ => ‖t‖^6) := by
    convert! (branchDelta_expansion hd).mul ((branchDelta_quadratic hd).add ht) using 1 <;>
      (funext t; ring)
  apply ((branchEnergy_amplitude_expansion hd).sub
    (hh.const_mul_left ((d:ℝ)/(2*kappa d)))).congr_left
  intro t
  have hk := (kappa_pos d hd).ne'
  field_simp
  ring

#print axioms branchEnergy_amplitude_expansion
#print axioms branchEnergy_delta_expansion
end BecknerOnofri.HighDim.DiagonalScalarBranch
