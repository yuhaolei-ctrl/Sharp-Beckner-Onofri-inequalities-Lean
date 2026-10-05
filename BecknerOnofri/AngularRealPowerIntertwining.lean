module

public import Legacy.BecknerOnofri.AngularSpectralIntertwining

@[expose] public section

/-! Real-power spectral intertwining on the actual Jacobi tensor Hilbert space.
This supplies the all-s spectral step. Identification of this spectral domain
with the manuscript's Friedrichs form closure is a separate obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.AngularRealPower
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev RadialWiener AngularMixedTerms AngularMixedL2
open JacobiTensor JacobiTensorSpectrum AngularSpectralIntertwining

lemma inverse_tensorVector {d : ℕ} (α : Index d) (hα : α ≠ 0)
    (s : ℝ) (hs : 0 < s) (n : Index d) :
    inversePower α hα s hs (tensorVector α n)=
      (tensorEigenvalue α n)^(-s) • tensorVector α n := by
  classical
  apply (hilbertBasis α).repr.injective
  ext l
  rw [repr_inversePower,← hilbertBasis_apply,map_smul,(hilbertBasis α).repr_self]
  by_cases he : n=l
  · subst l; simp
  · simp [lp.single_apply,he]

lemma real_multiplier {d : ℕ} (s : ℝ) (is : List (Fin d)) (k : Frequency d)
    (hk : ∀ i,is.count i≤(k i).natAbs) :
    (tensorEigenvalue (countIndex is) (shiftedIndex is k))^(-s)=
      (frequencyRadius k) ^ (-(2*s)) := by
  rw [shifted_eigenvalue is k hk,← Real.rpow_natCast (frequencyRadius k) 2,
    ← Real.rpow_mul (frequencyRadius_nonneg k)]
  congr 1
  push_cast
  ring

lemma term_intertwining {d : ℕ} (s : ℝ) (hs : 0 < s)
    (a b : Frequency d → ℂ)
    (hcoeff : ∀ k : Frequency d,k≠0 →
      a k=((frequencyRadius k ^ (-(2*s)) : ℝ):ℂ)*b k)
    (is : List (Fin d)) (his : is≠[]) (k : Frequency d) :
    termVector a is k=inversePower (countIndex is) (countIndex_ne_zero is his) s hs
      (termVector b is k) := by
  by_cases hk : ∀ i,is.count i≤(k i).natAbs
  · rw [termVector_eq_tensor a is k hk,termVector_eq_tensor b is k hk,map_smul,
      inverse_tensorVector,smul_smul,real_multiplier s is k hk]
    congr 1
    rw [hcoeff k (frequency_ne_zero is his k hk)]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  · push Not at hk
    obtain ⟨i,hi⟩ := hk
    rw [termVector_eq_zero a is k i hi,termVector_eq_zero b is k i hi,map_zero]

/-- Every positive real exponent, not only s=d/2. -/
theorem inverse_intertwining {d : ℕ} (s : ℝ) (hs : 0 < s)
    (a b : Frequency d → ℂ) (hb : ∀ m : ℕ,RadialSummable b m)
    (hcoeff : ∀ k : Frequency d,k≠0 →
      a k=((frequencyRadius k ^ (-(2*s)) : ℝ):ℂ)*b k)
    (is : List (Fin d)) (his : is≠[]) :
    vector a is=inversePower (countIndex is) (countIndex_ne_zero is his) s hs (vector b is) := by
  rw [vector,vector,(inversePower (countIndex is) (countIndex_ne_zero is his) s hs).map_tsum
    (termVector_norm_summable b hb is).of_norm]
  exact tsum_congr (term_intertwining s hs a b hcoeff is his)

lemma inverse_injective {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s) :
    Function.Injective (inversePower α hα s hs) := by
  intro u v he
  apply (hilbertBasis α).repr.injective
  ext n
  have h := congrArg (fun w => (hilbertBasis α).repr w n) he
  simp only [repr_inversePower] at h
  have hp : 0 < tensorEigenvalue α n := (positiveSpectrum α hα).value_pos n
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos hp (-s)).ne' h

/-- The graph of the positive spectral power: inversePower is everywhere
bounded and injective, so this graph is single valued on its range. -/
def PowerGraph {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    (u v : TensorL2 d) : Prop := inversePower α hα s hs v=u

lemma powerGraph_unique {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    {u v w : TensorL2 d} (hv : PowerGraph α hα s hs u v) (hw : PowerGraph α hα s hs u w) :
    v=w := inverse_injective α hα s hs (hv.trans hw.symm)

lemma powerGraph_repr {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    {u v : TensorL2 d} (h : PowerGraph α hα s hs u v) (n : Index d) :
    (hilbertBasis α).repr v n=(tensorEigenvalue α n)^s*(hilbertBasis α).repr u n := by
  have hp : 0 < tensorEigenvalue α n := (positiveSpectrum α hα).value_pos n
  rw [← h,repr_inversePower,← mul_assoc,← Real.rpow_add hp]
  simp

/-- Actual all-s differentiated Fourier intertwining, stated as the graph of
the genuine positive diagonal operator. -/
theorem positive_intertwining {d : ℕ} (s : ℝ) (hs : 0<s)
    (a b : Frequency d → ℂ) (hb : ∀ m : ℕ,RadialSummable b m)
    (hcoeff : ∀ k : Frequency d,k≠0 →
      b k=((frequencyRadius k ^ (2*s) : ℝ):ℂ)*a k)
    (is : List (Fin d)) (his : is≠[]) :
    PowerGraph (countIndex is) (countIndex_ne_zero is his) s hs (vector a is) (vector b is) := by
  apply Eq.symm
  apply inverse_intertwining s hs a b hb (is := is) (his := his)
  intro k hk
  rw [hcoeff k hk,← mul_assoc,← Complex.ofReal_mul,
    ← Real.rpow_add (frequencyRadius_pos hk)]
  simp

#print axioms inverse_intertwining
#print axioms powerGraph_unique
#print axioms powerGraph_repr
#print axioms positive_intertwining
end BecknerOnofri.AngularRealPower
