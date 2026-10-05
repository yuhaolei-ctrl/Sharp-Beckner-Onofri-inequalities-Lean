import BecknerOnofri.LocalElevenCore.FullHessianDecomposition
import BecknerOnofri.GibbsPerturbation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy
open ContinuousGibbs ContinuousFirstShell GraphHessian FullHessianDecomposition

def value {d : ℕ} (μ : ℝ) (u : Space d) : ℝ :=
  logPartitionReal u-(1/(2*μ))*normalizedPotentialEnergy u

theorem value_eq_dual {d : ℕ} (hd : 0<d) (μ : ℝ) (u : Space d) (hm : MeanZero u) :
    dualFunctional (μ*spectralThreshold d) u=(value μ u : EReal) := by
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  change mean d u=0 at hm
  rw [dualFunctional,logPartition_eq_centeredLogPartition,centeredLogPartition_eq,hm,sub_zero,
    ← EReal.coe_sub]
  congr 1
  unfold value
  congr 1
  congr 1
  field_simp

theorem energy_smul {d : ℕ} (t : ℝ) (q : Space d) :
    normalizedPotentialEnergy (t • q)=t^2*normalizedPotentialEnergy q := by
  have ht (k : NonzeroFrequency d) : potentialTerm (t • q) k=t^2*potentialTerm q k := by
    simp only [potentialTerm,← coefficient_eq_fourierCoeff,map_smul,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs]
    ring
  simp only [normalizedPotentialEnergy,potentialEnergy,ht,tsum_mul_left]
  ring

theorem pairing_smul_right {d : ℕ} (t : ℝ) (u q : Space d) :
    normalizedEnergyPairing u (t • q)=t*normalizedEnergyPairing u q := by
  have hc (k : Frequency d) : fourierCoeff (t • (q : Torus d → ℝ)) k=
      (t:ℂ)*fourierCoeff q k := by
    calc
      _=coefficient k (t • q) := (coefficient_eq_fourierCoeff k (t • q)).symm
      _=_ := by rw [map_smul,coefficient_eq_fourierCoeff]; rfl
  unfold normalizedEnergyPairing
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [hc]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,add_zero]
  ring

theorem energy_line {d : ℕ} (hd : 0<d) (u q : Space d)
    (hu : InCriticalSobolev u) (hq : InCriticalSobolev q) (t : ℝ) :
    normalizedPotentialEnergy (u+t • q)=normalizedPotentialEnergy u+
      2*t*normalizedEnergyPairing u q+t^2*normalizedPotentialEnergy q := by
  have h := normalizedEnergy_add hd u (t • q) hu (GraphCritical.critical_smul t q hq)
  change normalizedPotentialEnergy (u+t • q)=normalizedPotentialEnergy u+
    2*normalizedEnergyPairing u (t • q)+normalizedPotentialEnergy (t • q) at h
  rw [energy_smul,pairing_smul_right] at h
  convert h using 1 <;> ring

def lineDerivative {d : ℕ} (μ : ℝ) (u q : Space d) (t : ℝ) : ℝ :=
  weightedMean (u+t • q) q-(1/μ)*(normalizedEnergyPairing u q+t*normalizedPotentialEnergy q)

theorem value_line_hasDerivAt {d : ℕ} (hd : 0<d) (μ : ℝ) (u q : Space d)
    (hu : InCriticalSobolev u) (hq : InCriticalSobolev q) (t : ℝ) :
    HasDerivAt (fun t : ℝ => value μ (u+t • q)) (lineDerivative μ u q t) t := by
  have hp : HasDerivAt (fun t : ℝ => u+t • q) q t := by
    convert! ((hasDerivAt_id t).smul_const q).const_add u using 1 <;> simp
  have hlog := (hasFDerivAt_logPartitionReal (u+t • q)).comp_hasDerivAt t hp
  have hpoly : HasDerivAt (fun s : ℝ => normalizedPotentialEnergy u+
      2*s*normalizedEnergyPairing u q+s^2*normalizedPotentialEnergy q)
      (2*normalizedEnergyPairing u q+2*t*normalizedPotentialEnergy q) t := by
    convert! ((hasDerivAt_id t).const_mul (2*normalizedEnergyPairing u q)).add
      (((hasDerivAt_id t).pow 2).mul_const (normalizedPotentialEnergy q)) |>.const_add
        (normalizedPotentialEnergy u) using 1
    · ext s
      simp only [Pi.add_apply,Pi.pow_apply,id_eq]
      ring
    · try simp only [one_mul,pow_one,id_eq]
      ring
  convert! hlog.sub (hpoly.const_mul (1/(2*μ))) using 1
  · ext s
    simp only [value,energy_line hd u q hu hq s,Function.comp_def,Pi.sub_apply]
  · simp only [lineDerivative,div_eq_mul_inv,mul_inv_rev,one_mul]
    norm_num
    ring

theorem lineDerivative_hasDerivAt {d : ℕ} (hd : 0<d) (μ : ℝ) (u q : Space d) (t : ℝ) :
    HasDerivAt (lineDerivative μ u q)
      (secondVariation (μ*spectralThreshold d) (u+t • q) q) t := by
  have h := GibbsPerturbation.expectation_line_hasDerivAt u q q t
  have hpoly := (((hasDerivAt_id t).mul_const (normalizedPotentialEnergy q)).const_add
    (normalizedEnergyPairing u q)).const_mul (1/μ)
  convert! h.sub hpoly using 1
  rw [secondVariation,physical_factor hd,logPartitionHessian_apply]
  simp only [weightedMean_apply,mean_apply,ContinuousMap.mul_apply,normalized_apply,one_mul,pow_two]

#print axioms value_line_hasDerivAt
#print axioms lineDerivative_hasDerivAt
end BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy
