module

public import BecknerOnofri.SelectedCubicSymmetry
public import Legacy.BecknerOnofri.CoordinatePolarization

@[expose] public section

/-! Coordinate reflections of every nonnegative Fourier-coefficient global
optimizer. The strict Ginibre argument does not select a special optimizer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment
open ContinuousGibbs ContinuousFirstShell GinibreCovariance

def frequencyFlip {d : ℕ} (i : Fin d) : Frequency d ≃+ Frequency d where
  toFun k j := if j=i then -k j else k j
  invFun k j := if j=i then -k j else k j
  left_inv k := by ext j; by_cases hj : j=i <;> simp [hj]
  right_inv k := by ext j; by_cases hj : j=i <;> simp [hj]
  map_add' k l := by ext j; by_cases hj : j=i <;> simp [hj,add_comm]

@[simp] lemma frequencyFlip_toEquiv_apply {d : ℕ} (i : Fin d) (k : Frequency d) :
    (frequencyFlip i).toEquiv k=frequencyFlip i k := rfl

lemma frequencyFlip_involutive {d : ℕ} (i : Fin d) : Function.Involutive (frequencyFlip i) :=
  (frequencyFlip i).left_inv

@[simp] lemma frequencyFlip_flip {d : ℕ} (i : Fin d) (k : Frequency d) :
    frequencyFlip i (frequencyFlip i k)=k := (frequencyFlip i).left_inv k

lemma radius_flip {d : ℕ} (i : Fin d) (k : Frequency d) :
    frequencyRadius (frequencyFlip i k)=frequencyRadius k := by
  unfold frequencyRadius
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [frequencyFlip,hj]

lemma Domain.flipped {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (i : Fin d) :
    Domain (fun k => a (frequencyFlip i k)) where
  nonneg k := ha.nonneg _
  even k := by rw [map_neg,ha.even]
  zero := by rw [map_zero]; exact ha.zero
  summable := (frequencyFlip i).toEquiv.summable_iff.mpr ha.summable
  weighted := by
    have hs := (frequencyFlip i).toEquiv.summable_iff.mpr ha.weighted
    exact hs.congr (fun k => by simp only [Function.comp_def,frequencyFlip_toEquiv_apply,energyTerm,radius_flip])

lemma energy_flipped {d : ℕ} (a : Frequency d → ℝ) (i : Fin d) :
    energy (fun k => a (frequencyFlip i k))=energy a := by
  have he := (frequencyFlip i).toEquiv.tsum_eq (energyTerm a)
  simpa only [energy,energyTerm,frequencyFlip_toEquiv_apply,radius_flip] using he

lemma mFourier_coordinate_reflection {d : ℕ} (i : Fin d) (k : Frequency d) (x : Torus d) :
    UnitAddTorus.mFourier k (CoordinatePolarization.reflection i 0 x)=
      UnitAddTorus.mFourier (frequencyFlip i k) x := by
  simp only [UnitAddTorus.mFourier,ContinuousMap.coe_mk]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i
  · simp [CoordinatePolarization.reflection,CoordinatePolarization.circleReflection,
      frequencyFlip,hj,fourier_apply,zsmul_neg,neg_zsmul]
  · simp [CoordinatePolarization.reflection,frequencyFlip,hj]

lemma series_flipped {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a)
    (i : Fin d) (x : Torus d) :
    cosineSeries (fun k => a (frequencyFlip i k)) id x=
      cosineSeries a id (CoordinatePolarization.reflection i 0 x) := by
  rw [series_re _ (ha.flipped i).nonneg (ha.flipped i).summable,
    series_re _ ha.nonneg ha.summable]
  congr 1
  unfold absoluteFourierSeries
  simp_rw [mFourier_coordinate_reflection]
  have he := (frequencyFlip i).toEquiv.tsum_eq
    (fun k => (a k : ℂ)*UnitAddTorus.mFourier (frequencyFlip i k) x)
  simpa only [frequencyFlip_toEquiv_apply,frequencyFlip_flip] using he

lemma functional_flipped {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a)
    (i : Fin d) (A : ℝ) :
    functional A (toPotential (fun k => a (frequencyFlip i k)))=functional A (toPotential a) := by
  rw [toPotential_functional (ha.flipped i),toPotential_functional ha,energy_flipped]
  congr 1
  simp only [logPartitionReal,ContinuousGibbs.partition,mean_apply,exponential_apply]
  congr 1
  simp_rw [series_flipped ha]
  exact CoordinatePolarization.reflection_integral i 0 (fun x => Real.exp (cosineSeries a id x))

/-- Every actual maximizer is fixed by each coordinate reflection. -/
theorem maximizer_reflection_coefficients {d : ℕ} (hd : 0 < d)
    {a : Frequency d → ℝ} (ha : Domain a) {A : ℝ} (hA : 0 < A)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A (toPotential a))
    (i : Fin d) (k : Frequency d) : a (frequencyFlip i k)=a k := by
  have he := involutive_maximizer_coefficients hd ha (ha.flipped i) (frequencyFlip i)
    (frequencyFlip_involutive i) (fun _ => rfl) hA hmax (functional_flipped ha i A)
  exact (congrFun he k).symm

#print axioms maximizer_reflection_coefficients
end BecknerOnofri.HighDim.CosineCoefficientLattice
