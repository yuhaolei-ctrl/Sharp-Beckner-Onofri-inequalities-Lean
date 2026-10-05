import BecknerOnofri.InvolutiveMaximizerSymmetry
import BecknerOnofri.PermutationSymmetry
import Mathlib.GroupTheory.Perm.Sign

/-! Actual coordinate-permutation symmetry of nonnegative Fourier maximizers.
The support and strict Ginibre arguments are applied to transpositions, then
Mathlib's swap induction gives every coordinate permutation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment
open ContinuousGibbs ContinuousFirstShell ContinuousSymmetry GinibreCovariance

def frequencyEquiv {d : ℕ} (σ : Equiv.Perm (Fin d)) : Frequency d ≃+ Frequency d where
  toFun := frequencyPermutation σ
  invFun := frequencyPermutation σ.symm
  left_inv k := by ext i; simp [frequencyPermutation]
  right_inv k := by ext i; simp [frequencyPermutation]
  map_add' _ _ := rfl

@[simp] theorem frequencyEquiv_apply {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyEquiv σ k=frequencyPermutation σ k := rfl

@[simp] theorem frequencyRadius_permutation {d : ℕ} (σ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyRadius (frequencyPermutation σ k)=frequencyRadius k :=
  frequencyLength_permutation σ k

theorem Domain.permuted {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (σ : Equiv.Perm (Fin d)) :
    Domain (fun k => a (frequencyPermutation σ k)) where
  nonneg k := ha.nonneg _
  even k := by rw [frequencyPermutation_neg,ha.even]
  zero := by
    rw [show frequencyPermutation σ 0=0 from (frequencyPermutation_eq_zero_iff σ 0).mpr rfl]
    exact ha.zero
  summable := (frequencyEquiv σ).toEquiv.summable_iff.mpr ha.summable
  weighted := by
    have hh := (frequencyEquiv σ).toEquiv.summable_iff.mpr ha.weighted
    apply hh.congr
    intro k
    change frequencyRadius (frequencyPermutation σ k)^d*a (frequencyPermutation σ k)^2=
      frequencyRadius k^d*a (frequencyPermutation σ k)^2
    rw [frequencyRadius_permutation]

theorem energy_permuted {d : ℕ} (a : Frequency d → ℝ) (σ : Equiv.Perm (Fin d)) :
    energy (fun k => a (frequencyPermutation σ k))=energy a := by
  have hh := (frequencyEquiv σ).toEquiv.tsum_eq (energyTerm a)
  calc
    _ = ∑' k,energyTerm a ((frequencyEquiv σ).toEquiv k) := by
      apply tsum_congr
      intro k
      change frequencyRadius k^d*a (frequencyPermutation σ k)^2=
        frequencyRadius (frequencyPermutation σ k)^d*a (frequencyPermutation σ k)^2
      rw [frequencyRadius_permutation]
    _ = _ := hh

theorem series_permuted {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (σ : Equiv.Perm (Fin d)) :
    cosineSeries (fun k => a (frequencyPermutation σ k)) id=permutation σ (cosineSeries a id) := by
  apply coefficient_ext
  intro k
  rw [coefficient_permutation,series_coefficient _ (ha.permuted σ).nonneg
    (ha.permuted σ).summable (ha.permuted σ).even,series_coefficient _ ha.nonneg ha.summable ha.even]

theorem functional_permuted {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a)
    (σ : Equiv.Perm (Fin d)) (A : ℝ) :
    functional A (toPotential (fun k => a (frequencyPermutation σ k)))=functional A (toPotential a) := by
  rw [toPotential_functional (ha.permuted σ),toPotential_functional ha,energy_permuted,
    series_permuted ha,logPartitionReal,partition_permutation]
  rfl

theorem maximizer_swap_coefficients {d : ℕ} (hd : 0<d) {a : Frequency d → ℝ} (ha : Domain a)
    {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a))
    (i j : Fin d) (k : Frequency d) : a (frequencyPermutation (Equiv.swap i j) k)=a k := by
  classical
  have he : Function.Involutive (frequencyEquiv (Equiv.swap i j)) := by
    intro k
    ext n
    simp [frequencyEquiv,frequencyPermutation]
  have hh := involutive_maximizer_coefficients hd ha (ha.permuted (Equiv.swap i j))
    (frequencyEquiv (Equiv.swap i j)) he (fun _ => rfl) hA hmax (functional_permuted ha (Equiv.swap i j) A)
  exact (congrFun hh k).symm

theorem frequencyPermutation_mul {d : ℕ} (σ τ : Equiv.Perm (Fin d)) (k : Frequency d) :
    frequencyPermutation (σ*τ) k=frequencyPermutation σ (frequencyPermutation τ k) := rfl

/-- Every nonnegative actual coefficient maximizer is invariant under all
coordinate permutations; no symmetry is among the hypotheses. -/
theorem maximizer_permutation_coefficients {d : ℕ} (hd : 0<d) {a : Frequency d → ℝ} (ha : Domain a)
    {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a))
    (σ : Equiv.Perm (Fin d)) (k : Frequency d) : a (frequencyPermutation σ k)=a k := by
  classical
  induction σ using Equiv.Perm.swap_induction_on generalizing k with
  | one => rfl
  | swap_mul σ i j hij ih =>
    rw [frequencyPermutation_mul,maximizer_swap_coefficients hd ha hA hmax]
    exact ih k

open SelectedNumericalModel PositiveFourierSupport

theorem selected_domain {u : TorusL2 12} (hu : Selected u) : Domain (amplitude u) where
  nonneg := amplitude_nonneg hu
  even := selected_amplitude_even hu
  zero := amplitude_zero hu
  summable := amplitude_summable hu
  weighted := by
    apply hu.1.2.2.congr
    intro k
    simp only [weightedSquare,energyTerm,fourier_eq_amplitude hu,Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem selected_toPotential {u : TorusL2 12} (hu : Selected u) : toPotential (amplitude u)=u := by
  apply (fourierIsometry 12).injective
  ext k
  rw [toPotential_coefficient (selected_domain hu),fourier_eq_amplitude hu]

theorem selected_permutation_amplitude {u : TorusL2 12} (hu : Selected u)
    (σ : Equiv.Perm (Fin 12)) (k : Frequency 12) :
    amplitude u (frequencyPermutation σ k)=amplitude u k := by
  apply maximizer_permutation_coefficients (by norm_num) (selected_domain hu) (by norm_num : (0:ℝ)<1/2)
  intro v hv
  rw [selected_toPotential hu]
  exact hu.2.1 v hv

theorem selected_permutation_potential {u : TorusL2 12} (hu : Selected u)
    (σ : Equiv.Perm (Fin 12)) : permutation σ (potential u)=potential u := by
  rw [potential,← series_permuted (selected_domain hu)]
  congr 1
  funext k
  exact selected_permutation_amplitude hu σ k

private def signPoint {d : ℕ} (S : Finset (Fin d)) (x : Torus d) : Torus d :=
  fun i => if i∈S then -x i else x i

private theorem separately_even_signPoint {d : ℕ} (f : Torus d → ℝ)
    (hf : ∀ i x,f (Function.update x i (-x i))=f x) (S : Finset (Fin d)) (x : Torus d) :
    f (signPoint S x)=f x := by
  classical
  induction S using Finset.induction_on with
  | empty => congr 1
  | @insert i S hi ih =>
    have he : signPoint (insert i S) x=Function.update (signPoint S x) i (-signPoint S x i) := by
      ext j
      by_cases hj : j=i
      · subst j; simp [signPoint,hi]
      · simp [signPoint,hi,hj,Function.update_apply]
    rw [he,hf,ih]

/-- The selected actual potential has the complete signed-permutation
invariance required for hyperoctahedral orbit compression. -/
theorem selected_signed_permutation_potential {u : TorusL2 12} (hu : Selected u)
    (σ : Equiv.Perm (Fin 12)) (ε : Fin 12 → ℤ) (hε : ∀ i,ε i=1 ∨ ε i= -1) (x : Torus 12) :
    potential u (fun i => ε i • x (σ i))=potential u x := by
  classical
  let y : Torus 12 := fun i => x (σ i)
  have hreflect : ∀ i z,potential u (Function.update z i (-z i))=potential u z := by
    intro i z
    simp_rw [potential_apply hu]
    exact hu.2.2.2.1 i z
  have hsign : (fun i => ε i • y i)=signPoint (Finset.univ.filter (fun i => ε i= -1)) y := by
    ext i
    rcases hε i with hi | hi <;> simp [signPoint,hi]
  have hy : potential u y=potential u x := by
    have he := congrArg (fun f : ContinuousGibbs.Space 12 => f x) (selected_permutation_potential hu σ.symm)
    change potential u (pointPermutation σ.symm x)=potential u x at he
    have heq : pointPermutation σ.symm x=y := by ext i; simp [pointPermutation_apply,y]
    rw [heq] at he
    exact he
  change potential u (fun i => ε i • y i)=_
  rw [hsign,separately_even_signPoint (potential u) hreflect,hy]

theorem selected_permutation_densityFourier {u : TorusL2 12} (hu : Selected u)
    (σ : Equiv.Perm (Fin 12)) (k : Frequency 12) :
    densityFourier (SubcriticalEuler.gibbsValue u) (frequencyPermutation σ k)=
      densityFourier (SubcriticalEuler.gibbsValue u) k := by
  have he : permutation σ (normalized (potential u))=normalized (potential u) := by
    rw [← normalized_permutation,selected_permutation_potential hu]
  have hh := congrArg (coefficient k) he
  rw [coefficient_permutation,density_coefficient hu,density_coefficient hu] at hh
  exact hh

/-- Coordinate reflections of actual selected Gibbs modes follow directly
from the proved positive cosine-power mixture, whose factors depend on |k_i|. -/
theorem selected_densityFourier_same_abs {u : TorusL2 12} (hu : Selected u)
    (k l : Frequency 12) (habs : ∀ i,(k i).natAbs=(l i).natAbs) :
    densityFourier (SubcriticalEuler.gibbsValue u) k=densityFourier (SubcriticalEuler.gibbsValue u) l := by
  obtain ⟨w,N,hw,hm,hSup,heq⟩ := GenericCosineRepresentation.steiner_maximizer_mixture
    (by norm_num : 0<12) (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  rw [← SmoothFourier.smoothGibbsDensity_fourier SelectedNumericalModel.rough hu.1 (fourier_norm_summable hu) k,
    ← SmoothFourier.smoothGibbsDensity_fourier SelectedNumericalModel.rough hu.1 (fourier_norm_summable hu) l]
  change densityFourier (SmoothFourier.smoothGibbsValue u) k=densityFourier (SmoothFourier.smoothGibbsValue u) l
  rw [heq,CosineMixtureTransfer.rho_fourier w N hw hm.summable,
    CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  congr 1
  apply tsum_congr
  intro n
  congr 1
  unfold RandomRectangles.componentCoeff
  congr 1
  exact funext habs

#print axioms maximizer_permutation_coefficients
#print axioms selected_permutation_amplitude
#print axioms selected_signed_permutation_potential
#print axioms selected_permutation_densityFourier
#print axioms selected_densityFourier_same_abs
end BecknerOnofri.HighDim.CosineCoefficientLattice
