import BecknerOnofri.Uniform
import BecknerOnofri.GreenCritical
import BecknerOnofri.CircleOuterParseval
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Constructions

/-! Parseval controls the genuine Fourier energy of a continuous perturbation;
all nonzero modes of 1+t*h are exactly t times the corresponding mode of h. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.UniformFourier
open ContinuousGibbs ContinuousFirstShell

lemma smooth_continuous {d : ℕ} {h : Torus d → ℝ} (hh : SmoothOnTorus h) : Continuous h := by
  have hq : IsOpenQuotientMap (fun x : Fin d → ℝ => fun i => (x i:UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ : Fin d => QuotientAddGroup.isOpenQuotientMap_mk)
  exact hq.isQuotientMap.continuous_iff.mpr hh.continuous

lemma parseval {d : ℕ} (h : Space d) :
    HasSum (fun k => ‖fourierCoeff h k‖^2) (∫ x, (h x)^2 ∂torusMeasure d) := by
  let f : C(Torus d,ℂ) := ⟨fun x => (h x:ℂ), Complex.continuous_ofReal.comp h.continuous⟩
  have he (k : Frequency d) : UnitAddTorus.mFourierCoeff f k = fourierCoeff h k := rfl
  have hi : (∫ x, Complex.normSq (f x) ∂torusMeasure d) = ∫ x, (h x)^2 ∂torusMeasure d := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [f, Complex.normSq, pow_two])
  simpa only [he, hi] using CircleOuter.boundary_parseval f

def energy {d : ℕ} (h : Torus d → ℝ) : ℝ :=
  ∑' k : NonzeroFrequency d, (frequencyLength k.val^d)⁻¹ * ‖fourierCoeff h k.val‖^2

lemma term_bound {d : ℕ} (h : Space d) (k : NonzeroFrequency d) :
    0 ≤ (frequencyLength k.val^d)⁻¹ * ‖fourierCoeff h k.val‖^2 ∧
    (frequencyLength k.val^d)⁻¹ * ‖fourierCoeff h k.val‖^2 ≤ ‖fourierCoeff h k.val‖^2 := by
  constructor
  · unfold frequencyLength; positivity
  · exact mul_le_of_le_one_left (sq_nonneg _)
      (inv_le_one_of_one_le₀ (GreenCritical.nonzero_eigenvalue_ge_one k))

lemma energy_summable {d : ℕ} (h : Space d) :
    Summable (fun k : NonzeroFrequency d => (frequencyLength k.val^d)⁻¹ * ‖fourierCoeff h k.val‖^2) :=
  ((parseval h).summable.subtype _).of_nonneg_of_le (fun k => (term_bound h k).1) (fun k => (term_bound h k).2)

lemma energy_le_square {d : ℕ} (h : Space d) : energy h ≤ ∫ x, (h x)^2 ∂torusMeasure d := by
  calc
    _ ≤ ∑' k : NonzeroFrequency d, ‖fourierCoeff h k.val‖^2 :=
      (energy_summable h).tsum_le_tsum (fun k => (term_bound h k).2) ((parseval h).summable.subtype _)
    _ ≤ ∑' k : Frequency d, ‖fourierCoeff h k‖^2 :=
      ((parseval h).summable.subtype _).tsum_le_tsum_of_inj (fun k => k.val) Subtype.val_injective
        (fun _ _ => sq_nonneg _) (fun _ => le_rfl) (parseval h).summable
    _ = _ := (parseval h).tsum_eq

lemma perturbation_fourier {d : ℕ} (h : Space d) (t : ℝ) (k : NonzeroFrequency d) :
    fourierCoeff (fun x => 1+t*h x) k.val = (t:ℂ)*fourierCoeff h k.val := by
  change fourierCoeff (1+t • h : Space d) k.val = _
  rw [← coefficient_eq_fourierCoeff, map_add, map_smul, coefficient_eq_fourierCoeff,
    coefficient_eq_fourierCoeff]
  change fourierCoeff (fun _ : Torus d => 1) k.val + (t:ℂ)*fourierCoeff h k.val = _
  rw [fourierCoeff_one_nonzero k.val k.property, zero_add]

lemma perturbation_energy {d : ℕ} (h : Space d) (t : ℝ) :
    energy (fun x => 1+t*h x) = t^2*energy h := by
  unfold energy
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [perturbation_fourier, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

#print axioms energy_le_square
#print axioms perturbation_energy
end BecknerOnofri.HighDim.UniformFourier
