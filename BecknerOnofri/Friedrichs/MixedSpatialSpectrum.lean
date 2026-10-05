module

public import BecknerOnofri.Friedrichs.MixedTensorBasis
public import BecknerOnofri.Friedrichs.MixedCoordinateNormalization
public import BecknerOnofri.Friedrichs.MixedGraphClosed

@[expose] public section

/-! Full mixed spatial/spectral equivalence. No coordinate is replaced by a half-circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def mixedEigenvalue {d : ℕ} (α n : MultiIndex d) : ℝ :=
  ∑ i,(coordinateFrequency (α i) (n i):ℝ)^2

lemma basisTensorVector_eq_full {d : ℕ} (α n : MultiIndex d) :
    basisTensorVector α n=(∏ i,coordinateScalar (α i) (n i)) •
      fullEigenvector α (fun i => coordinateFrequency (α i) (n i))
        (fun i => coordinateOdd (α i) (n i)) := by
  let ns : MultiIndex d := fun i => coordinateFrequency (α i) (n i)
  let os : Fin d → Bool := fun i => coordinateOdd (α i) (n i)
  have hr := (profile_memLp α (fullEigenprofiles α ns os) (fullEigenprofiles_smooth α ns os)).coeFn_toLp
  apply Lp.ext
  filter_upwards [basisTensorVector_ae_eq α n,
    Lp.coeFn_smul (∏ i,coordinateScalar (α i) (n i)) (fullEigenvector α ns os),hr] with x hx hs hv
  change fullEigenvector α ns os x=productProfile (fullEigenprofiles α ns os) x at hv
  rw [hx,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hv,basisTensorFunction,coordinateFunction_eq_raw,
    Finset.prod_mul_distrib,productProfile,fullEigenprofiles,ns,os]

lemma basisTensorVector_operatorGraph {d : ℕ} (α n : MultiIndex d) :
    operatorGraph α (basisTensorVector α n) (mixedEigenvalue α n • basisTensorVector α n) := by
  rw [basisTensorVector_eq_full]
  have h := operatorGraph_smul (fullEigenvector_operatorGraph α
    (fun i => coordinateFrequency (α i) (n i)) (fun i => coordinateOdd (α i) (n i)))
    (∏ i,coordinateScalar (α i) (n i))
  simpa only [mixedEigenvalue,smul_smul,mul_comm] using h

lemma mixed_operatorGraph_repr {d : ℕ} (α : MultiIndex d) {f g : H α}
    (h : operatorGraph α f g) (n : MultiIndex d) :
    (mixedHilbertBasis α).repr g n=mixedEigenvalue α n*(mixedHilbertBasis α).repr f n := by
  have he := operatorGraph_symmetric h (basisTensorVector_operatorGraph α n)
  simpa only [HilbertBasis.repr_apply_apply,mixedHilbertBasis_apply,real_inner_comm,inner_smul_right] using he

theorem mixed_operatorGraph_iff_repr {d : ℕ} (α : MultiIndex d) (f g : H α) :
    operatorGraph α f g ↔ ∀ n,(mixedHilbertBasis α).repr g n=
      mixedEigenvalue α n*(mixedHilbertBasis α).repr f n := by
  constructor
  · exact fun h n => mixed_operatorGraph_repr α h n
  · intro h
    let b := mixedHilbertBasis α
    obtain ⟨s,hs⟩ : ∃ s : ℕ → Finset (MultiIndex d),Tendsto s atTop atTop := exists_seq_tendsto atTop
    let fN (N : ℕ) : H α := ∑ n∈s N,b.repr f n • b n
    let gN (N : ℕ) : H α := ∑ n∈s N,b.repr g n • b n
    have hf : Tendsto fN atTop (𝓝 f) := (b.hasSum_repr f).comp hs
    have hg : Tendsto gN atTop (𝓝 g) := (b.hasSum_repr g).comp hs
    apply operatorGraph_of_tendsto hf hg
    intro N
    apply operatorGraph_sum
    intro n hn
    have he := operatorGraph_smul (basisTensorVector_operatorGraph α n) (b.repr f n)
    simpa only [b,mixedHilbertBasis_apply,smul_smul,h n,mul_comm] using he

theorem mixed_operatorGraph_iff_coefficients {d : ℕ} (α : MultiIndex d) (f g : H α) :
    operatorGraph α f g ↔ ∀ n,inner ℝ g (basisTensorVector α n)=
      mixedEigenvalue α n*inner ℝ f (basisTensorVector α n) := by
  simpa only [HilbertBasis.repr_apply_apply,mixedHilbertBasis_apply,real_inner_comm] using
    mixed_operatorGraph_iff_repr α f g

theorem mixed_operatorGraph_selfAdjoint {d : ℕ} (α : MultiIndex d) (h k : H α) :
    operatorGraph α h k ↔ ∀ f g : H α,operatorGraph α f g → inner ℝ g h=inner ℝ f k := by
  constructor
  · exact fun hh f g hfg => operatorGraph_symmetric hfg hh
  · intro ht
    apply (mixed_operatorGraph_iff_coefficients α h k).mpr
    intro n
    have he := ht _ _ (basisTensorVector_operatorGraph α n)
    simpa only [inner_smul_left,conj_trivial,real_inner_comm] using he.symm

#print axioms mixed_operatorGraph_iff_coefficients
#print axioms mixed_operatorGraph_selfAdjoint
end BecknerOnofri.Friedrichs.MixedSpatial
