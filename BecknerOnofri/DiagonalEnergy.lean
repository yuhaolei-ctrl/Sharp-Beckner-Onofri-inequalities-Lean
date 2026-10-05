import BecknerOnofri.RealDiagonalReduction
import BecknerOnofri.ReducedEnergyGradient

/-! The actual physical energy along the symmetric real diagonal, with its
exact scalar variational equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.DiagonalEnergy
open ContinuousGibbs ContinuousFirstShell GreenLocalBranch ReducedEquation
open ReducedCubicExpansion RealDiagonalReduction ReducedEnergyGradient

def diagonalEnergy {d : ℕ} (hd : 12 ≤ d) (x : ℝ × ℝ) : ℝ :=
  physicalReducedEnergy hd (diagonalEmbedding d x)

theorem hasDerivAt_diagonalEnergy {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), HasDerivAt
      (fun t => diagonalEnergy hd (x.1,t)) (-(2*(d:ℝ)/x.1)*diagonalResidual hd x) x.2 := by
  have hp : ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [(diagonalEmbedding_tendsto d).eventually (hasFDerivAt_physicalReducedEnergy hd),
    reduced_realDiagonal hd, hp] with x hx hr hpos
  have hh := hx.comp x.2 (realDiagonal d).hasFDerivAt
  have hc : graphGradient x.1 (fun z => correction hd (x.1,z)) (realDiagonal d x.2) (realDiagonal d 1) =
      -(2*(d:ℝ)/x.1)*diagonalResidual hd x := by
    rw [graphGradient_apply hpos.ne']
    change -(2/x.1) * (∑ i, conj (realDiagonal d 1 i) *
      reduced hd (x.1,realDiagonal d x.2) i).re = _
    rw [hr]
    simp only [realDiagonal_apply, Complex.ofReal_one, map_one, one_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  convert! hh.hasDerivAt using 1
  exact hc.symm

theorem deriv_diagonalEnergy {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      deriv (fun t => diagonalEnergy hd (x.1,t)) x.2 =
        -(2*(d:ℝ)/x.1)*diagonalResidual hd x := by
  filter_upwards [hasDerivAt_diagonalEnergy hd] with x hx
  exact hx.deriv

theorem diagonalEnergy_critical_iff {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0),
      deriv (fun t => diagonalEnergy hd (x.1,t)) x.2 = 0 ↔ diagonalResidual hd x = 0 := by
  have hp : ∀ᶠ x : ℝ × ℝ in 𝓝 (1,0), 0 < x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [deriv_diagonalEnergy hd,hp] with x hx hpos
  rw [hx, mul_eq_zero]
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0<d by omega)
  have hc : -(2*(d:ℝ)/x.1) ≠ 0 := neg_ne_zero.mpr (div_ne_zero (mul_ne_zero (by norm_num) hdpos.ne') hpos.ne')
  exact or_iff_right (fun h => hc h)

#print axioms hasDerivAt_diagonalEnergy
end BecknerOnofri.HighDim.DiagonalEnergy
