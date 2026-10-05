module

public import BecknerOnofri.SelectedMarginalParseval
public import BecknerOnofri.ContinuousMarginal

@[expose] public section

/-! The common actual one-coordinate marginal of a selected maximizer satisfies
the source twelfth-root L² bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open ContinuousGibbs ContinuousMarginal

/-- Actual normalized Gibbs density integrated in the other eleven coordinates. -/
def selectedMarginal (u : TorusL2 12) (i : Fin 12) : C(UnitAddCircle,ℝ) :=
  marginal i (normalized (potential u))

def marginalNorm (u : TorusL2 12) (i : Fin 12) : ℝ :=
  Real.sqrt (∫ s,(selectedMarginal u i s)^2 ∂AddCircle.haarAddCircle)

theorem selectedMarginal_fourier {u : TorusL2 12} (hu : Selected u) (i : Fin 12) (n : ℤ) :
    _root_.fourierCoeff (fun s => (selectedMarginal u i s : ℂ)) n=(axisMode u n : ℂ) := by
  rw [selectedMarginal,marginal_fourier]
  rw [← ContinuousFirstShell.coefficient_eq_fourierCoeff]
  rw [density_coefficient hu,densityFourier_eq_mode hu,densityMode_axis hu]

theorem marginalNorm_sq {u : TorusL2 12} (hu : Selected u) (i : Fin 12) :
    marginalNorm u i^2=∑' n,axisMode u n^2 := by
  have h := circle_parseval (selectedMarginal u i)
  simp_rw [selectedMarginal_fourier hu,Complex.norm_real,Real.norm_eq_abs,sq_abs] at h
  rw [marginalNorm,Real.sq_sqrt (integral_nonneg (fun s => sq_nonneg _)),h.tsum_eq]

theorem marginalNorm_power_bound {u : TorusL2 12} (hu : Selected u) (i : Fin 12) :
    marginalNorm u i^12≤densityNorm u := by
  have hs : (marginalNorm u i^12)^2≤densityNorm u^2 := by
    rw [← pow_mul,show 12*2=2*12 by norm_num,pow_mul,marginalNorm_sq hu]
    exact axisMode_power_bound hu
  exact (sq_le_sq₀ (pow_nonneg (Real.sqrt_nonneg _) _) (Real.sqrt_nonneg _)).mp hs

/-- The source marginal bound for the genuine Fubini marginal, with no
unproved independence or product structure assumption. -/
theorem selected_marginal_cap {u : TorusL2 12} (hu : Selected u) (i : Fin 12)
    {M : ℝ} (hM : densityNorm u≤M) :
    marginalNorm u i≤M^((1:ℝ)/12) := by
  have hMn : 0≤M := (Real.sqrt_nonneg _).trans hM
  rw [one_div,Real.le_rpow_inv_iff_of_pos (show 0≤marginalNorm u i from Real.sqrt_nonneg _) hMn (by norm_num : (0:ℝ)<12)]
  rw [show (12:ℝ)=(12:ℕ) by norm_num,Real.rpow_natCast]
  exact (marginalNorm_power_bound hu i).trans hM

#print axioms selectedMarginal_fourier
#print axioms selected_marginal_cap
end BecknerOnofri.HighDim.SelectedNumericalModel
