module

public import BecknerOnofri.Friedrichs.MixedSpatialSpectrum

@[expose] public section

/-! Spectral powers of the self-adjoint realization of the actual mixed spatial graph.
The complete mixed basis includes all periodic odd sectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def SpectralPowerGraph {d : ℕ} (α : MultiIndex d) (s : ℝ) (f g : H α) : Prop :=
  ∀ n,inner ℝ g (basisTensorVector α n)=(mixedEigenvalue α n)^s*inner ℝ f (basisTensorVector α n)

lemma spectralPowerGraph_one {d : ℕ} (α : MultiIndex d) (f g : H α) :
    SpectralPowerGraph α 1 f g ↔ operatorGraph α f g := by
  simpa only [SpectralPowerGraph,Real.rpow_one] using (mixed_operatorGraph_iff_coefficients α f g).symm

lemma spectralPowerGraph_unique {d : ℕ} {α : MultiIndex d} {s : ℝ} {f g h : H α}
    (hg : SpectralPowerGraph α s f g) (hh : SpectralPowerGraph α s f h) : g=h := by
  apply sub_eq_zero.mp
  apply basisTensorVector_total α (g-h)
  intro n
  rw [inner_sub_left,hg n,hh n,sub_self]

lemma spectralPowerGraph_domain {d : ℕ} (α : MultiIndex d) (s : ℝ) (f : H α) :
    (∃ g,SpectralPowerGraph α s f g) ↔
      Memℓp (fun n => (mixedEigenvalue α n)^s*(mixedHilbertBasis α).repr f n) 2 := by
  have he (g : H α) : SpectralPowerGraph α s f g ↔
      ∀ n,(mixedHilbertBasis α).repr g n=(mixedEigenvalue α n)^s*(mixedHilbertBasis α).repr f n := by
    simp only [SpectralPowerGraph,HilbertBasis.repr_apply_apply,mixedHilbertBasis_apply,real_inner_comm]
  constructor
  · rintro ⟨g,hg⟩
    have hr := funext ((he g).mp hg)
    rw [← hr]
    exact lp.memℓp _
  · intro h
    refine ⟨(mixedHilbertBasis α).repr.symm ⟨_,h⟩,(he _).mpr ?_⟩
    intro n
    exact congrArg (fun x : lp (fun _ : MultiIndex d => ℝ) 2 => x n)
      ((mixedHilbertBasis α).repr.apply_symm_apply _)

lemma spectralPowerGraph_closed {d : ℕ} (α : MultiIndex d) (s : ℝ) :
    IsClosed {p : H α×H α | SpectralPowerGraph α s p.1 p.2} := by
  simp only [SpectralPowerGraph,setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_eq <;> fun_prop

lemma spectralPowerGraph_zero {d : ℕ} (α : MultiIndex d) (s : ℝ) :
    SpectralPowerGraph α s 0 0 := by intro n; simp

lemma spectralPowerGraph_add {d : ℕ} {α : MultiIndex d} {s : ℝ} {f g h k : H α}
    (hf : SpectralPowerGraph α s f g) (hh : SpectralPowerGraph α s h k) :
    SpectralPowerGraph α s (f+h) (g+k) := by
  intro n
  simp only [inner_add_left,hf n,hh n,mul_add]

lemma spectralPowerGraph_smul {d : ℕ} {α : MultiIndex d} {s : ℝ} {f g : H α}
    (hf : SpectralPowerGraph α s f g) (c : ℝ) : SpectralPowerGraph α s (c • f) (c • g) := by
  intro n
  simp only [inner_smul_left,conj_trivial,hf n]
  ring

lemma spectralPowerGraph_sum {d : ℕ} {α : MultiIndex d} {s : ℝ} {I : Type*}
    (S : Finset I) (f g : I → H α) (h : ∀ i∈S,SpectralPowerGraph α s (f i) (g i)) :
    SpectralPowerGraph α s (∑ i∈S,f i) (∑ i∈S,g i) := by
  intro n
  simp only [sum_inner,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => h i hi n)

lemma spectralPowerGraph_hasSum {d : ℕ} {α : MultiIndex d} {s : ℝ} {I : Type*}
    (f g : I → H α) {F G : H α} (hf : HasSum f F) (hg : HasSum g G)
    (h : ∀ i,SpectralPowerGraph α s (f i) (g i)) : SpectralPowerGraph α s F G := by
  apply (spectralPowerGraph_closed α s).mem_of_tendsto (hf.prodMk_nhds hg)
  exact Eventually.of_forall (fun S => spectralPowerGraph_sum S f g (fun i _ => h i))

lemma spectralPowerGraph_eigenvector {d : ℕ} {α : MultiIndex d} {f : H α} {ev : ℝ}
    (hf : operatorGraph α f (ev • f)) (s : ℝ) : SpectralPowerGraph α s f (ev^s • f) := by
  intro n
  have he := (mixed_operatorGraph_iff_coefficients α f (ev • f)).mp hf n
  simp only [inner_smul_left,conj_trivial] at he ⊢
  by_cases hz : inner ℝ f (basisTensorVector α n)=0
  · simp [hz]
  · rw [mul_right_cancel₀ hz he]

#print axioms spectralPowerGraph_domain
#print axioms spectralPowerGraph_closed
#print axioms spectralPowerGraph_eigenvector
end BecknerOnofri.Friedrichs.MixedSpatial
