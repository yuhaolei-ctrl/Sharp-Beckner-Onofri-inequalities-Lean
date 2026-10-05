module

public import BecknerOnofri.Friedrichs.MixedChebyshevEigenvectors
public import BecknerOnofri.Friedrichs.MixedGraphClosed
public import Legacy.BecknerOnofri.JacobiTensorCompleteness

@[expose] public section

/-! Exact spatial/spectral identification when every coordinate is active.
The inactive periodic sectors require a separate full-periodic basis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial
namespace Active
open Legacy.BecknerOnofri

 def index {d : ℕ} (a : MultiIndex d) : MultiIndex d := fun i => a i+1

lemma measure_eq {d : ℕ} (a : MultiIndex d) : spatialMeasure (index a)=JacobiTensor.measure d := rfl

lemma tensorVector_eq_chebyshev {d : ℕ} (a n : MultiIndex d) :
    (JacobiTensor.tensorVector (index a) n : H (index a))=
      JacobiTensor.normalizationFactor (index a) n •
        chebyshevVector (index a) (fun i => n i+index a i) := by
  apply Lp.ext
  have ha := (angular_memLp (index a) (chebyshevProfiles (index a) (fun i => n i+index a i))
    (chebyshevProfiles_smooth (index a) (fun i => n i+index a i))).coeFn_toLp
  filter_upwards [JacobiTensor.tensorVector_ae_eq (index a) n,
    Lp.coeFn_smul (JacobiTensor.normalizationFactor (index a) n)
      (chebyshevVector (index a) (fun i => n i+index a i)),ha] with x hx hs hv
  change chebyshevVector (index a) (fun i => n i+index a i) x=
    angularFunction (index a) (chebyshevProfiles (index a) (fun i => n i+index a i)) x at hv
  rw [hx,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hv,JacobiTensor.tensorFunction_eq_raw]
  rw [JacobiTensor.tensorPolynomial_apply]
  rfl

lemma tensorVector_operatorGraph {d : ℕ} (a n : MultiIndex d) :
    operatorGraph (index a) (JacobiTensor.tensorVector (index a) n)
      (JacobiTensor.tensorEigenvalue (index a) n • JacobiTensor.tensorVector (index a) n) := by
  rw [tensorVector_eq_chebyshev]
  have he := operatorGraph_smul (chebyshevVector_operatorGraph (index a) (fun i => n i+index a i))
    (JacobiTensor.normalizationFactor (index a) n)
  simpa only [JacobiTensor.tensorEigenvalue,JacobiEigenfunctions.eigenvalue,smul_smul,mul_comm] using he

lemma operatorGraph_repr {d : ℕ} (a : MultiIndex d) {f g : H (index a)}
    (h : operatorGraph (index a) f g) (n : MultiIndex d) :
    (JacobiTensor.hilbertBasis (index a)).repr g n=JacobiTensor.tensorEigenvalue (index a) n*
      (JacobiTensor.hilbertBasis (index a)).repr f n := by
  have he := operatorGraph_symmetric h (tensorVector_operatorGraph a n)
  simpa only [HilbertBasis.repr_apply_apply,JacobiTensor.hilbertBasis_apply,real_inner_comm,inner_smul_right] using he

theorem operatorGraph_iff_repr {d : ℕ} (a : MultiIndex d) (f g : H (index a)) :
    operatorGraph (index a) f g ↔ ∀ n,(JacobiTensor.hilbertBasis (index a)).repr g n=
      JacobiTensor.tensorEigenvalue (index a) n*(JacobiTensor.hilbertBasis (index a)).repr f n := by
  constructor
  · exact fun h n => operatorGraph_repr a h n
  · intro h
    let b := JacobiTensor.hilbertBasis (index a)
    obtain ⟨s,hs⟩ : ∃ s : ℕ → Finset (MultiIndex d),Tendsto s atTop atTop := exists_seq_tendsto atTop
    let fN (N : ℕ) : H (index a) := ∑ n∈s N,b.repr f n • b n
    let gN (N : ℕ) : H (index a) := ∑ n∈s N,b.repr g n • b n
    have hf : Tendsto fN atTop (𝓝 f) := (b.hasSum_repr f).comp hs
    have hg : Tendsto gN atTop (𝓝 g) := (b.hasSum_repr g).comp hs
    apply operatorGraph_of_tendsto hf hg
    intro N
    apply operatorGraph_sum
    intro n hn
    have he := operatorGraph_smul (tensorVector_operatorGraph a n) (b.repr f n)
    simpa only [b,JacobiTensor.hilbertBasis_apply,smul_smul,h n,mul_comm] using he

#print axioms operatorGraph_iff_repr
end Active
end BecknerOnofri.Friedrichs.MixedSpatial
