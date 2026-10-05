module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.GraphHessianFourier
public import BecknerOnofri.LocalElevenCore.ReducedEnergyGradient
public import BecknerOnofri.LocalElevenCore.ComplementHessian

@[expose] public section

/-! Genuine Fourier-energy identities for differentiated complementary equations. -/
noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.GraphHessian

open BecknerOnofri.HighDim.GraphHessian hiding linearized_energy_term linearized_fourier_euler linearized_inCriticalSobolev linearized_normalizedEnergy linearized_pairing_complement normalizedEnergyPairing normalizedEnergyPairing_self weighted_norm_pairing
open BecknerOnofri.HighDim.QuadraticModes
open ContinuousGibbs ContinuousFirstShell ContinuousComplement QuadraticModes
open BecknerOnofri.HighDim.GraphCritical hiding critical_of_same_complement critical_smul firstShell_finite potential_inCriticalSobolev reconstruction_critical_of_projected
open BecknerOnofri.HighDim.GraphEnergy hiding assembly_square_mean complement_fourier_euler graph_dualFunctional graph_energy_term graph_normalizedEnergy_hasSum graph_normalizedPotentialEnergy graph_potentialEnergy hasSum_pairing hasSum_square
open BecknerOnofri.HighDim.GreenCritical hiding coefficient_square_summable green_inCriticalSobolev nonzero_eigenvalue_ge_one potentialTerm_green
open BecknerOnofri.HighDim.GreenPairing hiding coefficient_projectedGreen green_one mean_mul_green mean_mul_projectedGreen mean_mul_selfAdjoint_of_multiplier mean_projectedGreen projectedGreen projectedGreen_apply projectedGreen_one projectedGreen_sub_one
open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum
open GreenPairing GraphEnergy GraphCritical GreenCritical RawComplementGap

theorem linearized_fourier_euler {d : ℕ} (hd : 0<d) (μ : ℝ)
    (w : complement d) (a : Space d) (hw : (w : Space d)=μ • projectedGreen d a)
    (k : Frequency d) (hk : ComplementFrequency k) :
    ((frequencyLength k^d : ℝ):ℂ)*coefficient k (w : Space d) = (μ:ℂ)*coefficient k a := by
  have hc := congrArg (fun v : Space d => coefficient k v) hw
  rw [map_smul,coefficient_projectedGreen hd,if_pos hk] at hc
  have hlam : frequencyLength k^d ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (nonzero_eigenvalue_ge_one ⟨k,hk.1⟩)).ne'
  rw [hc]
  change ((frequencyLength k^d:ℝ):ℂ)*((μ:ℂ)*(((1/frequencyLength k^d:ℝ):ℂ)*coefficient k a)) = _
  have hinv : ((frequencyLength k^d:ℝ):ℂ)*((1/frequencyLength k^d:ℝ):ℂ)=1 := by
    rw [← Complex.ofReal_mul]
    simp [hlam]
  calc
    _ = (μ:ℂ)*((((frequencyLength k^d:ℝ):ℂ)*((1/frequencyLength k^d:ℝ):ℂ))*coefficient k a) := by ring
    _ = _ := by rw [hinv,one_mul]

theorem linearized_inCriticalSobolev {d : ℕ} (hd : 0<d) (μ : ℝ)
    (z : Coordinates d) (w : complement d) (a : Space d)
    (hw : (w : Space d)=μ • projectedGreen d a) :
    InCriticalSobolev (reconstruction d (z,w)) := by
  apply critical_of_same_complement _ (μ • greenContinuous d a)
    (critical_smul μ _ (green_inCriticalSobolev hd a))
  intro k hk
  have hv : coefficient k (assembly d z)=0 := by
    rw [← projection_assembly z]
    exact coefficient_projection_off_shell _ _ hk.2
  rw [reconstruction_apply,map_add,hv,zero_add,hw,map_smul,map_smul,
    coefficient_projectedGreen hd,if_pos hk,coefficient_green hd,if_neg hk.1]

theorem weighted_norm_pairing {a b : ℂ} {lam μ : ℝ}
    (he : (lam:ℂ)*a=(μ:ℂ)*b) : lam*‖a‖^2=μ*(conj a*b).re := by
  have hh := congrArg Complex.re (congrArg (fun q : ℂ => conj a*q) he)
  have hl : conj a*((lam:ℂ)*a)=(lam:ℂ)*(conj a*a) := by ring
  have hr : conj a*((μ:ℂ)*b)=(μ:ℂ)*(conj a*b) := by ring
  rw [hl,hr,← Complex.normSq_eq_conj_mul_self] at hh
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.normSq_eq_norm_sq] using hh

theorem linearized_energy_term {d : ℕ} (hd : 0<d) (μ : ℝ)
    (z : Coordinates d) (w : complement d) (a : Space d)
    (hw : (w : Space d)=μ • projectedGreen d a) (k : Frequency d) :
    frequencyLength k^d*‖coefficient k (reconstruction d (z,w))‖^2 =
      ‖coefficient k (assembly d z)‖^2+μ*(conj (coefficient k (w : Space d))*coefficient k a).re := by
  by_cases hk : ComplementFrequency k
  · have hv : coefficient k (assembly d z)=0 := by
      rw [← projection_assembly z]
      exact coefficient_projection_off_shell _ _ hk.2
    simp only [reconstruction_apply,map_add,hv,zero_add,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact weighted_norm_pairing (linearized_fourier_euler hd μ w a hw k hk)
  · have hc : coefficient k (w : Space d)=0 := (mem_complement_fourier_iff _).mp w.property k hk
    simp only [reconstruction_apply,map_add,hc,add_zero,map_zero,zero_mul,Complex.zero_re,mul_zero,add_zero]
    by_cases hk0 : k=0
    · subst k
      rw [coefficient_zero,mean_assembly]
      simp
    · have hs : InFirstShell k := Classical.byContradiction (fun hs => hk ⟨hk0,hs⟩)
      have hlam : frequencyLength k^d=1 := by
        rw [frequencyLength_pow_eq,(latticeSquare_eq_one_iff k).mpr hs]
        simp
      rw [hlam,one_mul]

theorem linearized_normalizedEnergy {d : ℕ} (hd : 0<d) (μ : ℝ)
    (z : Coordinates d) (w : complement d) (a : Space d)
    (hw : (w : Space d)=μ • projectedGreen d a) :
    normalizedPotentialEnergy (reconstruction d (z,w)) =
      2*∑ i : Fin d, ‖z i‖^2+μ*mean d ((w : Space d)*a) := by
  have hh := (hasSum_square (assembly d z)).add ((hasSum_pairing (w : Space d) a).mul_left μ)
  rw [assembly_square_mean] at hh
  have hsum := hh.congr_fun (fun k => linearized_energy_term hd μ z w a hw k)
  have hraw := raw_normalizedEnergy_hasSum hd _ (linearized_inCriticalSobolev hd μ z w a hw)
  simp only [← coefficient_eq_fourierCoeff] at hraw
  exact hraw.unique hsum

/-- The actual bilinear Fourier energy, paired on the full lattice. -/
def normalizedEnergyPairing {d : ℕ} (v q : Torus d → ℝ) : ℝ :=
  ∑' k : Frequency d, frequencyLength k^d*(conj (fourierCoeff v k)*fourierCoeff q k).re

theorem normalizedEnergyPairing_self {d : ℕ} (hd : 0<d) (v : Torus d → ℝ)
    (hv : InCriticalSobolev v) : normalizedEnergyPairing v v=normalizedPotentialEnergy v := by
  unfold normalizedEnergyPairing
  have he (k : Frequency d) : (conj (fourierCoeff v k)*fourierCoeff v k).re=‖fourierCoeff v k‖^2 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  simp only [he]
  exact (raw_normalizedEnergy_hasSum hd v hv).tsum_eq

theorem linearized_pairing_complement {d : ℕ} (hd : 0<d) (μ : ℝ)
    (z : Coordinates d) (w q : complement d) (a : Space d)
    (hw : (w : Space d)=μ • projectedGreen d a) :
    normalizedEnergyPairing (reconstruction d (z,w)) (q : Space d)=μ*mean d (a*(q : Space d)) := by
  have he (k : Frequency d) :
      frequencyLength k^d*(conj (coefficient k (reconstruction d (z,w)))*coefficient k (q : Space d)).re =
        μ*(conj (coefficient k a)*coefficient k (q : Space d)).re := by
    by_cases hk : ComplementFrequency k
    · have hz : coefficient k (assembly d z)=0 := by
        rw [← projection_assembly z]
        exact coefficient_projection_off_shell _ _ hk.2
      have hh := congrArg (fun v : ℂ => (conj v*coefficient k (q : Space d)).re)
        (linearized_fourier_euler hd μ w a hw k hk)
      simp only [reconstruction_apply,map_add,hz,zero_add]
      simpa only [map_mul,Complex.conj_ofReal,Complex.mul_re,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,zero_add,mul_assoc] using hh
    · rw [(mem_complement_fourier_iff _).mp q.property k hk]
      simp
  have hh := ((hasSum_pairing a (q : Space d)).mul_left μ).congr_fun he
  simpa only [normalizedEnergyPairing,← coefficient_eq_fourierCoeff] using hh.tsum_eq

#print axioms linearized_normalizedEnergy
#print axioms linearized_pairing_complement
end BecknerOnofri.HighDim.LocalEleven.GraphHessian
