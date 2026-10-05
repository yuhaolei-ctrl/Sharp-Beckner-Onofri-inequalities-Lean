module

public import BecknerOnofri.Friedrichs.ProductL2Totality
public import BecknerOnofri.Friedrichs.MixedCoordinateBasis

@[expose] public section

/-! Completeness of all mixed sine/cosine--Jacobi products on the actual mixed measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def basisTensorFunction {d : ℕ} (α : MultiIndex d) (k : Fin d → ℕ) (x : Space d) : ℝ :=
  ∏ i,coordinateFunction (α i) (k i) (x i)

lemma basisTensorFunction_memLp {d : ℕ} (α : MultiIndex d) (k : Fin d → ℕ) :
    MemLp (basisTensorFunction α k) 2 (spatialMeasure α) :=
  continuous_memLp α (continuous_finsetProd _ (fun i _ =>
    (coordinateFunction_smooth (α i) (k i)).continuous.comp (continuous_apply i)))

theorem basisTensorFunction_total_ae (d : ℕ) (α : MultiIndex d) {F : Space d → ℝ}
    (hF : MemLp F 2 (spatialMeasure α))
    (h : ∀ k : Fin d → ℕ,(∫ x,basisTensorFunction α k x*F x ∂spatialMeasure α)=0) :
    F=ᵐ[spatialMeasure α] 0 := by
  induction d with
  | zero =>
    have he : F=fun _ => F 0 := funext (fun x => congrArg F (Subsingleton.elim x 0))
    have hz := h (fun i => Fin.elim0 i)
    rw [he] at hz
    simp [basisTensorFunction,spatialMeasure,Measure.real,Measure.pi_univ] at hz
    exact ae_of_all _ (fun x => (congrArg F (Subsingleton.elim x ![])).trans hz)
  | succ d ih =>
    let α' : MultiIndex d := fun i => α i.succ
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
    have hp := measurePreserving_piFinSuccAbove (fun i => coordinateMeasure (α i)) 0
    have hFp : MemLp (F ∘ e.symm) 2 ((coordinateMeasure (α 0)).prod (spatialMeasure α')) :=
      hF.comp_measurePreserving hp.symm
    have hzero : (F ∘ e.symm)=ᵐ[(coordinateMeasure (α 0)).prod (spatialMeasure α')] 0 := by
      apply ProductL2.tensor_total
        (coordinateFunction (α 0))
        (basisTensorFunction α')
        (coordinateFunction_memLp (α 0))
        (basisTensorFunction_memLp α')
        (coordinateFunction_total (α 0))
        (fun f hf => by
          apply Lp.ext
          exact (ih α' (Lp.memLp f) hf).trans (Lp.coeFn_zero ℝ 2 (spatialMeasure α')).symm)
        hFp
      intro k l
      have he (p : ℝ×Space d) : basisTensorFunction α (Fin.cons k l) (e.symm p)=
          coordinateFunction (α 0) k p.1*basisTensorFunction α' l p.2 := by
        simp [basisTensorFunction,e,MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv,Fin.prod_univ_succ,α']
      have hh := h (Fin.cons k l)
      unfold spatialMeasure at hh
      rw [← hp.symm.integral_comp' (fun x => basisTensorFunction α (Fin.cons k l) x*F x)] at hh
      change (∫ p,basisTensorFunction α (Fin.cons k l) (e.symm p)*F (e.symm p)
        ∂(coordinateMeasure (α 0)).prod (spatialMeasure α'))=0 at hh
      simpa only [Function.comp_apply,he] using hh
    have hh := hp.quasiMeasurePreserving.ae hzero
    change ∀ᵐ x ∂spatialMeasure α,F x=0
    simpa only [spatialMeasure,e,Function.comp_apply,Pi.zero_apply,MeasurableEquiv.symm_apply_apply] using hh

theorem basisTensorFunction_total {d : ℕ} (α : MultiIndex d) (F : H α)
    (h : ∀ k : Fin d → ℕ,(∫ x,basisTensorFunction α k x*F x ∂spatialMeasure α)=0) : F=0 := by
  apply Lp.ext
  exact (basisTensorFunction_total_ae d α (Lp.memLp F) h).trans (Lp.coeFn_zero ℝ 2 (spatialMeasure α)).symm

def basisTensorVector {d : ℕ} (α : MultiIndex d) (k : Fin d → ℕ) : H α :=
  (basisTensorFunction_memLp α k).toLp (basisTensorFunction α k)

lemma basisTensorVector_ae_eq {d : ℕ} (α : MultiIndex d) (k : Fin d → ℕ) :
    basisTensorVector α k=ᵐ[spatialMeasure α] basisTensorFunction α k :=
  (basisTensorFunction_memLp α k).coeFn_toLp

lemma basisTensorVector_orthonormal {d : ℕ} (α : MultiIndex d) :
    Orthonormal ℝ (basisTensorVector α) := by
  rw [orthonormal_iff_ite]
  intro n l
  have he : inner ℝ (basisTensorVector α n) (basisTensorVector α l)=
      ∫ x,basisTensorFunction α n x*basisTensorFunction α l x ∂spatialMeasure α := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [basisTensorVector_ae_eq α n,basisTensorVector_ae_eq α l] with x hn hl
    simp only [hn,hl,RCLike.inner_apply,conj_trivial]
    ring
  rw [he]
  simp only [basisTensorFunction,← Finset.prod_mul_distrib,spatialMeasure]
  rw [integral_fintype_prod_eq_prod (μ := fun i => coordinateMeasure (α i))
    (fun i t => coordinateFunction (α i) (n i) t*coordinateFunction (α i) (l i) t)]
  simp only [coordinateFunction_integral]
  split_ifs with h
  · subst l
    simp
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

lemma basisTensorVector_total {d : ℕ} (α : MultiIndex d) (f : H α)
    (h : ∀ n,inner ℝ f (basisTensorVector α n)=0) : f=0 := by
  apply basisTensorFunction_total α f
  intro n
  have he := h n
  rw [L2.inner_def] at he
  calc
    _ = ∫ x,inner ℝ (f x) (basisTensorVector α n x) ∂spatialMeasure α := by
      apply integral_congr_ae
      filter_upwards [basisTensorVector_ae_eq α n] with x hx
      simp only [hx,RCLike.inner_apply,conj_trivial]
    _ = 0 := he

lemma basisTensorVector_orthogonalComplement {d : ℕ} (α : MultiIndex d) :
    (Submodule.span ℝ (range (basisTensorVector α)))ᗮ=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply basisTensorVector_total α f
  intro n
  exact Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self n)) hf

def mixedHilbertBasis {d : ℕ} (α : MultiIndex d) : HilbertBasis (Fin d → ℕ) ℝ (H α) :=
  HilbertBasis.mkOfOrthogonalEqBot (basisTensorVector_orthonormal α)
    (basisTensorVector_orthogonalComplement α)

@[simp] lemma mixedHilbertBasis_apply {d : ℕ} (α : MultiIndex d) (n : Fin d → ℕ) :
    mixedHilbertBasis α n=basisTensorVector α n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

#print axioms mixedHilbertBasis
end BecknerOnofri.Friedrichs.MixedSpatial
