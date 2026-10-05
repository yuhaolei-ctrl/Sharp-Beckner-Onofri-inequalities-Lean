import BecknerOnofri.BranchDefinitions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral

/-! Actual Haar translation identities for the trusted raw function definitions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BecknerOnofri.HighDim

local instance (d : ℕ) : Measure.IsAddRightInvariant (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

theorem translation_measurePreserving {d : ℕ} (a : Torus d) :
    MeasurePreserving (fun x : Torus d => x-a) (torusMeasure d) (torusMeasure d) :=
  measurePreserving_sub_right (torusMeasure d) a

@[simp] theorem translate_zero {d : ℕ} (u : Torus d → ℝ) : translate u 0 = u := by
  funext x
  simp [translate]

theorem translate_translate {d : ℕ} (u : Torus d → ℝ) (a b : Torus d) :
    translate (translate u a) b = translate u (a+b) := by
  funext x
  simp only [translate]
  congr 1
  abel

theorem integral_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    (∫ x, translate u a x ∂torusMeasure d) = ∫ x, u x ∂torusMeasure d :=
  integral_sub_right_eq_self u a

theorem memLp_translate_iff {d : ℕ} (u : Torus d → ℝ) (a : Torus d) (p : ℝ≥0∞) :
    MemLp (translate u a) p (torusMeasure d) ↔ MemLp u p (torusMeasure d) := by
  constructor
  · intro h
    have hh := h.comp_measurePreserving (translation_measurePreserving (-a))
    change MemLp (translate (translate u a) (-a)) p (torusMeasure d) at hh
    simpa only [translate_translate, add_neg_cancel, translate_zero] using hh
  · intro h
    exact h.comp_measurePreserving (translation_measurePreserving a)

theorem mFourier_add_argument {d : ℕ} (k : Frequency d) (x y : Torus d) :
    UnitAddTorus.mFourier k (x+y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_norm_apply {d : ℕ} (k : Frequency d) (x : Torus d) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

/-- Translation changes each Fourier coefficient by its exact unit character. -/
theorem fourierCoeff_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) (k : Frequency d) :
    fourierCoeff (translate u a) k = UnitAddTorus.mFourier (-k) a * fourierCoeff u k := by
  unfold fourierCoeff
  rw [← integral_add_right_eq_self
    (fun x => UnitAddTorus.mFourier (-k) x * (translate u a x : ℂ)) a]
  simp only [translate, add_sub_cancel_right, mFourier_add_argument]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

@[simp] theorem norm_fourierCoeff_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d)
    (k : Frequency d) : ‖fourierCoeff (translate u a) k‖ = ‖fourierCoeff u k‖ := by
  rw [fourierCoeff_translate, norm_mul, mFourier_norm_apply, one_mul]

@[simp] theorem fourierCoeff_translate_eq_zero_iff {d : ℕ} (u : Torus d → ℝ) (a : Torus d)
    (k : Frequency d) : fourierCoeff (translate u a) k = 0 ↔ fourierCoeff u k = 0 := by
  rw [← norm_eq_zero, norm_fourierCoeff_translate, norm_eq_zero]

@[simp] theorem potentialTerm_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d)
    (k : NonzeroFrequency d) : potentialTerm (translate u a) k = potentialTerm u k := by
  simp only [potentialTerm, norm_fourierCoeff_translate]

@[simp] theorem potentialEnergy_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    potentialEnergy (translate u a) = potentialEnergy u := by
  simp only [potentialEnergy, potentialTerm_translate]

@[simp] theorem inCriticalSobolev_translate_iff {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    InCriticalSobolev (translate u a) ↔ InCriticalSobolev u := by
  have he : potentialTerm (translate u a) = potentialTerm u := funext (potentialTerm_translate u a)
  simp only [InCriticalSobolev, memLp_translate_iff, he]

@[simp] theorem sobolevTerm_translate {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (a : Torus d)
    (k : Frequency d) : sobolevTerm s (translate u a) k = sobolevTerm s u k := by
  simp only [sobolevTerm, norm_fourierCoeff_translate]

@[simp] theorem inSobolev_translate_iff {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    InSobolev s (translate u a) ↔ InSobolev s u := by
  have he : sobolevTerm s (translate u a) = sobolevTerm s u := funext (sobolevTerm_translate s u a)
  simp only [InSobolev, memLp_translate_iff, he]

@[simp] theorem sobolevNorm_translate {d : ℕ} (s : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    sobolevNorm s (translate u a) = sobolevNorm s u := by
  simp only [sobolevNorm, sobolevTerm_translate]

@[simp] theorem meanZero_translate_iff {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    MeanZero (translate u a) ↔ MeanZero u := by
  simp only [MeanZero, integral_translate]

theorem centered_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    centered (translate u a) = translate (centered u) a := by
  funext x
  change u (x-a) - (∫ y, translate u a y ∂torusMeasure d) =
    u (x-a) - (∫ y, u y ∂torusMeasure d)
  rw [integral_translate]

@[simp] theorem logPartition_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    logPartition (translate u a) = logPartition u := by
  unfold logPartition
  rw [centered_translate]
  congr 1
  exact lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (Real.exp (centered u x))) a

theorem normalizedGibbs_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) :
    normalizedGibbs (translate u a) = translate (normalizedGibbs u) a := by
  funext x
  unfold normalizedGibbs translate
  rw [integral_sub_right_eq_self (fun x => Real.exp (u x)) a]

@[simp] theorem dualFunctional_translate {d : ℕ} (β : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    dualFunctional β (translate u a) = dualFunctional β u := by
  simp only [dualFunctional, logPartition_translate, normalizedPotentialEnergy, potentialEnergy_translate]

def translateDensity {d : ℕ} (ρ : ProbabilityDensity d) (a : Torus d) : ProbabilityDensity d where
  value := translate ρ.value a
  nonneg := (translation_measurePreserving a).quasiMeasurePreserving.ae ρ.nonneg
  integrable := (translation_measurePreserving a).integrable_comp_of_integrable ρ.integrable
  mass := (integral_translate ρ.value a).trans ρ.mass

@[simp] theorem translateDensity_value {d : ℕ} (ρ : ProbabilityDensity d) (a : Torus d) :
    (translateDensity ρ a).value = translate ρ.value a := rfl

@[simp] theorem translateDensity_finiteEntropy_iff {d : ℕ} (ρ : ProbabilityDensity d) (a : Torus d) :
    (translateDensity ρ a).FiniteEntropy ↔ ρ.FiniteEntropy := by
  change Integrable ((fun x => ρ.value x*Real.log (ρ.value x)) ∘ (fun x => x-a)) (torusMeasure d) ↔ _
  apply (translation_measurePreserving a).integrable_comp_emb
  exact (MeasurableEquiv.subRight a).measurableEmbedding

@[simp] theorem entropy_translateDensity {d : ℕ} (ρ : ProbabilityDensity d) (a : Torus d) :
    entropy (translateDensity ρ a) = entropy ρ :=
  integral_sub_right_eq_self (fun x => ρ.value x*Real.log (ρ.value x)) a

@[simp] theorem spectralEnergy_translateDensity {d : ℕ} (ρ : ProbabilityDensity d) (a : Torus d) :
    spectralEnergy (translateDensity ρ a) = spectralEnergy ρ := by
  simp only [spectralEnergy, spectralTerm, translateDensity_value, norm_fourierCoeff_translate]

@[simp] theorem pressureValue_translateDensity {d : ℕ} (β : ℝ) (ρ : ProbabilityDensity d) (a : Torus d) :
    pressureValue β (translateDensity ρ a) = pressureValue β ρ := by
  simp only [pressureValue, spectralEnergy_translateDensity, entropy_translateDensity]

@[simp] theorem isGlobalMinimizer_translateDensity_iff {d : ℕ} (β : ℝ)
    (ρ : ProbabilityDensity d) (a : Torus d) :
    IsGlobalMinimizer β (translateDensity ρ a) ↔ IsGlobalMinimizer β ρ := by
  simp only [IsGlobalMinimizer, translateDensity_finiteEntropy_iff, pressureValue_translateDensity]

theorem coordinateDerivative_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d)
    (j : Fin d) : coordinateDerivative (translate u a) j = translate (coordinateDerivative u j) a := by
  funext x
  unfold coordinateDerivative translate
  congr 1
  funext t
  congr 1
  abel

theorem tangentCombination_translate {d : ℕ} (u : Torus d → ℝ) (a : Torus d) (c : Fin d → ℝ) :
    tangentCombination (translate u a) c = translate (tangentCombination u c) a := by
  funext x
  simp only [tangentCombination, coordinateDerivative_translate, translate]

@[simp] theorem secondVariation_translate {d : ℕ} (β : ℝ) (u h : Torus d → ℝ) (a : Torus d) :
    secondVariation β (translate u a) (translate h a) = secondVariation β u h := by
  unfold secondVariation
  rw [normalizedGibbs_translate]
  simp only [translate, normalizedPotentialEnergy, potentialEnergy_translate]
  rw [integral_sub_right_eq_self (fun x => normalizedGibbs u x * h x ^ 2) a,
    integral_sub_right_eq_self (fun x => normalizedGibbs u x * h x) a]

theorem firstShellProfile_eq_translate {d : ℕ} (a : Torus d) :
    firstShellProfile a = translate (firstShellProfile 0) a := by
  funext x
  simp only [firstShellProfile, translate, Pi.sub_apply, Pi.zero_apply, sub_zero]

theorem branchRemainder_eq_translate {d : ℕ} (β : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    branchRemainder β u a = translate (branchRemainder β u 0) a := by
  funext x
  simp only [branchRemainder, translate, firstShellProfile, Pi.sub_apply, Pi.zero_apply, sub_zero]

@[simp] theorem branchRemainder_sobolevNorm {d : ℕ} (s β : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    sobolevNorm s (branchRemainder β u a) = sobolevNorm s (branchRemainder β u 0) := by
  rw [branchRemainder_eq_translate, sobolevNorm_translate]

theorem branchRemainder_inSobolev_iff {d : ℕ} (s β : ℝ) (u : Torus d → ℝ) (a : Torus d) :
    InSobolev s (branchRemainder β u a) ↔ InSobolev s (branchRemainder β u 0) := by
  rw [branchRemainder_eq_translate, inSobolev_translate_iff]

#print axioms fourierCoeff_translate
#print axioms logPartition_translate
#print axioms spectralEnergy_translateDensity
#print axioms branchRemainder_sobolevNorm
end BecknerOnofri.HighDim
