module

public import Legacy.BecknerOnofri.CircleEqualityEnergy
public import Legacy.BecknerOnofri.SubcriticalWiener
public import Legacy.BecknerOnofri.CircleMilinEquality

@[expose] public section

/-! Actual positive Fourier data of a real circle potential. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators ComplexConjugate
namespace Legacy.BecknerOnofri.CircleEquality
open TorusSobolev SubcriticalAttainment SubcriticalEuler WienerFourier RadialWiener

 def positiveFourier (u : TorusL2 1) (n : ℕ) : ℂ := fourierIsometry 1 u (frequency (n : ℤ))

 theorem frequency_nat_injective : Function.Injective (fun n : ℕ => frequency (n : ℤ)) := by
  intro n m h
  have hh := congrFun h 0
  change (n : ℤ) = m at hh
  exact_mod_cast hh

 theorem positiveFourier_zero {u : TorusL2 1} (hu : Admissible u) : positiveFourier u 0 = 0 := hu.2.1

 theorem fourier_eq_coefficient {u : TorusL2 1} (hu : RealPotential u) (k : Frequency 1) :
    fourierIsometry 1 u k = coefficient (positiveFourier u) k := by
  cases h : k 0 with
  | ofNat n =>
    have hk : frequency (n : ℤ) = k := by simpa [h] using frequency_eq k
    simp only [coefficient,h,integerCoefficient]
    exact congrArg (fourierIsometry 1 u) hk.symm
  | negSucc n =>
    have hk : frequency (Int.negSucc n) = k := by
      simpa only [h] using frequency_eq k
    rw [← hk]
    change fourierIsometry 1 u (-frequency ((n+1 : ℕ) : ℤ)) =
      conj (fourierIsometry 1 u (frequency ((n+1 : ℕ) : ℤ)))
    exact fourier_real_symmetry hu _

 theorem positiveFourier_summable {u : TorusL2 1}
    (hu : Summable (fun k => ‖fourierIsometry 1 u k‖)) :
    Summable (fun n => ‖positiveFourier u n‖) := hu.comp_injective frequency_nat_injective

 theorem series_positiveFourier {u : TorusL2 1} (hu : RealPotential u) :
    series (positiveFourier u) = representative u := by
  unfold series representative
  congr 1
  exact funext (fun k => (fourier_eq_coefficient hu k).symm)

 theorem series_positiveFourier_ae {u : TorusL2 1} (hr : RealPotential u)
    (hu : Summable (fun k => ‖fourierIsometry 1 u k‖)) :
    series (positiveFourier u) =ᵐ[torusMeasure 1] u := by
  rw [series_positiveFourier hr]
  exact representative_ae_eq u hu

 theorem weighted_positiveFourier_summable {u : TorusL2 1} (hu : CriticalSobolev u) :
    Summable (fun n : ℕ => (n : ℝ)*‖positiveFourier u n‖^2) := by
  have h := hu.2.comp_injective frequency_nat_injective
  apply h.congr
  intro n
  simp [weightedSquare,frequencyRadius_one,positiveFourier]

 theorem positive_energy_eq {u : TorusL2 1} (hu : Admissible u) :
    criticalEnergy u = 2*(∑' n : ℕ,(n : ℝ)*‖positiveFourier u n‖^2) := by
  let e : ℕ → ℝ := fun n => (n : ℝ)*‖positiveFourier u n‖^2
  have hs : Summable e := weighted_positiveFourier_summable hu.2
  have he0 : e 0 = 0 := by simp [e]
  have ht : HasSum (fun n => e (n+1)) (∑' n,e n) := by
    have h := (hasSum_nat_add_iff' 1).mpr hs.hasSum
    simpa [he0] using h
  have hi : HasSum (fun j : ℤ => weightedSquare (fourierIsometry 1 u) (frequency j))
      ((∑' n,e n)+(∑' n,e n)) := by
    apply HasSum.of_nat_of_neg_add_one
    · convert! hs.hasSum using 1
      funext n
      simp [weightedSquare,frequencyRadius_one,positiveFourier,e]
    · convert! ht using 1
      funext n
      simp only [weightedSquare]
      rw [frequency_neg,fourier_real_symmetry hu.1]
      simp [frequencyRadius_one,positiveFourier,e,frequency]
      left
      rw [abs_of_nonpos (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)]
      ring
  have hfull : HasSum (weightedSquare (fourierIsometry 1 u)) ((∑' n,e n)+(∑' n,e n)) := by
    exact CosineMixtureAxis.frequencyOneEquivInt.symm.hasSum_iff.mp hi
  rw [criticalEnergy,coefficientEnergy,hfull.tsum_eq]
  dsimp [e]
  ring

 theorem onofri_energy_eq {u : TorusL2 1} (hu : Admissible u) :
    EndpointPotential.coefficient 1*criticalEnergy u =
      ∑' n : ℕ,(n : ℝ)*‖positiveFourier u n‖^2 := by
  rw [positive_energy_eq hu,EndpointPotential.coefficient,endpointConstant_one]
  ring

 theorem positiveFourier_decay {u : TorusL2 1}
    (hu : RadialSummable (fourierIsometry 1 u) 1) :
    Tendsto (fun n : ℕ => (n : ℂ)*positiveFourier u n) atTop (nhds 0) := by
  have hs := hu.comp_injective frequency_nat_injective
  have ht : Summable (fun n : ℕ => (n : ℝ)*‖positiveFourier u n‖) := by
    apply hs.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))
    intro n
    change (n : ℝ)*‖positiveFourier u n‖ ≤
      radialWeight 1 (frequency (n : ℤ))*‖positiveFourier u n‖
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simp [radialWeight,frequencyRadius_one]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul,Complex.norm_natCast] using ht.tendsto_atTop_zero

 theorem equality_positiveFourier_data (hE : Endpoint 1) {u : TorusL2 1}
    (hu : Admissible u)
    (he : Real.log (partition u) = EndpointPotential.coefficient 1*criticalEnergy u) :
    Summable (fun n => ‖positiveFourier u n‖) ∧
    Tendsto (fun n : ℕ => (n : ℂ)*positiveFourier u n) atTop (nhds 0) := by
  have hR := EndpointPotential.rough_of_endpoint (by decide : 0<1) hE
  have hA := EndpointPotential.coefficient_pos (by decide : 0<1)
  have hmax := EndpointPotential.maximizer_of_equality (by decide : 0<1) hE hu he
  exact ⟨positiveFourier_summable (maximizer_fourier_summable (by decide) hR hA hu hmax),
    positiveFourier_decay (maximizer_radialSummable (by decide) hR hA hu hmax 1)⟩

#print axioms equality_positiveFourier_data
#print axioms positive_energy_eq
end Legacy.BecknerOnofri.CircleEquality
