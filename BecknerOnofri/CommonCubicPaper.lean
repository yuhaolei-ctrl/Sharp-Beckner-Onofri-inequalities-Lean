import BecknerOnofri.GeneralCoefficientReflections
import BecknerOnofri.UniformFourierHessian

/-! The full signed-permutation symmetry statement for every smooth
nonnegative-Fourier global optimizer, without a selection hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open ContinuousGibbs ContinuousFirstShell ContinuousOptimizers ContinuousSymmetry GinibreCovariance

lemma optimizer_coefficient_domain {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hN : ∀ k : Frequency d, (fourierCoeff u k).im=0 ∧ 0≤(fourierCoeff u k).re)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u) :
    Domain (fun k => (coefficient k u).re) ∧
      toPotential (fun k => (coefficient k u).re)=toL2 d u ∧
      cosineSeries (fun k => (coefficient k u).re) id=u := by
  let a : Frequency d → ℝ := fun k => (coefficient k u).re
  have hn : ∀ k,0≤a k := by
    intro k
    simpa only [a,coefficient_eq_fourierCoeff] using (hN k).2
  have hc (k : Frequency d) : coefficient k u=(a k : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [coefficient_eq_fourierCoeff,Complex.ofReal_im] using (hN k).1
  have hU := OnsetContinuous.toL2_admissible hd u hu hm
  have hσ := spectralThreshold_pos hd
  have hA : 0 < spectralThreshold d/(2*β) := by positivity
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) hσ
  have hR := GenericAttainment.rough_bound hd
    (by positivity : 0 < endpointConstant d/2)
    (by linarith : endpointConstant d/2 < endpointConstant d)
  have hs := maximizer_fourier_summable hd hR hA hU (toL2_optimizer hd β u hu hm hmax)
  have ha : Domain a := by
    refine ⟨hn,?_,?_,?_,?_⟩
    · intro k
      simp only [a,coefficient_neg,Complex.conj_re]
    · change (coefficient 0 u).re=0
      rw [coefficient_zero,show mean d u=0 from hm]
      rfl
    · apply hs.congr
      intro k
      change ‖coefficient k u‖=a k
      rw [hc]
      simp [Complex.norm_real,abs_of_nonneg (hn k)]
    · apply hU.2.2.congr
      intro k
      change frequencyRadius k^d*‖coefficient k u‖^2=energyTerm a k
      rw [hc]
      simp only [energyTerm,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hseries : cosineSeries a id=u := by
    apply coefficient_ext
    intro k
    rw [series_coefficient a ha.nonneg ha.summable ha.even,hc]
  refine ⟨ha,?_,hseries⟩
  change toL2 d (cosineSeries a id)=toL2 d u
  rw [hseries]

lemma separately_even_all_signs {d : ℕ} (f : Torus d → ℝ)
    (hf : ∀ i x,f (Function.update x i (-x i))=f x)
    (ε : Fin d → ℤ) (hε : ∀ i,ε i=1 ∨ ε i= -1) (x : Torus d) :
    f (fun i => ε i • x i)=f x := by
  classical
  let signPoint (S : Finset (Fin d)) (x : Torus d) := fun i => if i∈S then -x i else x i
  have h (S : Finset (Fin d)) : f (signPoint S x)=f x := by
    induction S using Finset.induction_on with
    | empty => simpa [signPoint]
    | @insert i S hi ih =>
      have he : signPoint (insert i S) x=Function.update (signPoint S x) i (-signPoint S x i) := by
        ext j
        by_cases hj : j=i
        · subst j; simp [signPoint,hi]
        · simp [signPoint,hi,hj]
      rw [he,hf,ih]
  have he : (fun i => ε i • x i)=signPoint (Finset.univ.filter (fun i => ε i= -1)) x := by
    ext i
    rcases hε i with hi | hi <;> simp [signPoint,hi]
  rw [he]
  exact h _

theorem continuous_optimizer_signed_permutation {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Space d) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (hN : ∀ k : Frequency d, (fourierCoeff u k).im=0 ∧ 0≤(fourierCoeff u k).re)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (hε : ∀ i,ε i=1 ∨ ε i= -1) (x : Torus d) :
    u (fun i => ε i • x (σ i))=u x := by
  let a : Frequency d → ℝ := fun k => (coefficient k u).re
  obtain ⟨ha,hU,hseries⟩ := optimizer_coefficient_domain hd hβ u hu hm hN hmax
  have hA : 0 < spectralThreshold d/(2*β) := div_pos (spectralThreshold_pos hd) (by positivity)
  have hmaxa : ∀ V : TorusL2 d,Admissible V →
      functional (spectralThreshold d/(2*β)) V ≤ functional (spectralThreshold d/(2*β)) (toPotential a) := by
    rw [hU]
    exact toL2_optimizer hd β u hu hm hmax
  have href (i : Fin d) (z : Torus d) : u (Function.update z i (-z i))=u z := by
    have he := series_flipped ha i z
    have hc : (fun k => a (frequencyFlip i k))=a := funext (maximizer_reflection_coefficients hd ha hA hmaxa i)
    rw [hc,hseries] at he
    have hp : CoordinatePolarization.reflection i 0 z=Function.update z i (-z i) := by
      ext j
      by_cases hj : j=i <;> simp [CoordinatePolarization.reflection,
        CoordinatePolarization.circleReflection,Function.update_apply,hj]
    rw [hp] at he
    exact he.symm
  have hperm : permutation σ.symm u=u := by
    rw [← hseries,← series_permuted ha]
    congr 1
    exact funext (maximizer_permutation_coefficients hd ha hA hmaxa σ.symm)
  rw [separately_even_all_signs u href ε hε]
  have he := congrArg (fun v : Space d => v x) hperm
  change u (pointPermutation σ.symm x)=u x at he
  have hp : pointPermutation σ.symm x=(fun i => x (σ i)) := by
    ext i
    simp only [pointPermutation_apply,Equiv.symm_symm]
  rw [hp] at he
  exact he

/-- Literal pointwise source statement, with smoothness used to fix the
continuous representative of the original raw function. -/
theorem smooth_optimizer_signed_permutation {d : ℕ} (hd : 0 < d) {β : ℝ} (hβ : 0 < β)
    (u : Torus d → ℝ) (hu : InCriticalSobolev u) (hm : MeanZero u) (hs : SmoothOnTorus u)
    (hN : ∀ k : Frequency d, (fourierCoeff u k).im=0 ∧ 0≤(fourierCoeff u k).re)
    (hmax : ∀ v : Torus d → ℝ, InCriticalSobolev v → dualFunctional β v ≤ dualFunctional β u)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ℤ) (hε : ∀ i,ε i=1 ∨ ε i= -1) (x : Torus d) :
    u (fun i => ε i • x (σ i))=u x :=
  continuous_optimizer_signed_permutation hd hβ ⟨u,UniformFourier.smooth_continuous hs⟩ hu hm hN hmax σ ε hε x

#print axioms smooth_optimizer_signed_permutation
end BecknerOnofri.HighDim.CosineCoefficientLattice
