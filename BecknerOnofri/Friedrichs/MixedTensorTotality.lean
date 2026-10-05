import BecknerOnofri.Friedrichs.ProductL2Totality
import BecknerOnofri.Friedrichs.MixedCoordinateTotality

/-! Completeness of all mixed sine/cosine--Jacobi products on the actual mixed measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

abbrev ModeIndex := Bool×ℕ

def fullTensorFunction {d : ℕ} (α : MultiIndex d) (k : Fin d → ModeIndex) (x : Space d) : ℝ :=
  ∏ i,fullEigenprofile (α i) (k i).2 (k i).1 (x i)

lemma coordinate_fullEigenprofile_memLp (m n : ℕ) (odd : Bool) :
    MemLp (fullEigenprofile m n odd) 2 (coordinateMeasure m) :=
  (memLp_two_iff_integrable_sq (fullEigenprofile_smooth m n odd).continuous.aestronglyMeasurable).mpr
    (coordinate_square_integrable m (fullEigenprofile_smooth m n odd).continuous)

lemma fullTensorFunction_memLp {d : ℕ} (α : MultiIndex d) (k : Fin d → ModeIndex) :
    MemLp (fullTensorFunction α k) 2 (spatialMeasure α) :=
  continuous_memLp α (continuous_finsetProd _ (fun i _ =>
    (fullEigenprofile_smooth (α i) (k i).2 (k i).1).continuous.comp (continuous_apply i)))

theorem fullTensorFunction_total_ae (d : ℕ) (α : MultiIndex d) {F : Space d → ℝ}
    (hF : MemLp F 2 (spatialMeasure α))
    (h : ∀ k : Fin d → ModeIndex,(∫ x,fullTensorFunction α k x*F x ∂spatialMeasure α)=0) :
    F=ᵐ[spatialMeasure α] 0 := by
  induction d with
  | zero =>
    have he : F=fun _ => F 0 := funext (fun x => congrArg F (Subsingleton.elim x 0))
    have hz := h (fun i => Fin.elim0 i)
    rw [he] at hz
    simp [fullTensorFunction,spatialMeasure,Measure.real,Measure.pi_univ] at hz
    exact ae_of_all _ (fun x => (congrArg F (Subsingleton.elim x ![])).trans hz)
  | succ d ih =>
    let α' : MultiIndex d := fun i => α i.succ
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
    have hp := measurePreserving_piFinSuccAbove (fun i => coordinateMeasure (α i)) 0
    have hFp : MemLp (F ∘ e.symm) 2 ((coordinateMeasure (α 0)).prod (spatialMeasure α')) :=
      hF.comp_measurePreserving hp.symm
    have hzero : (F ∘ e.symm)=ᵐ[(coordinateMeasure (α 0)).prod (spatialMeasure α')] 0 := by
      apply ProductL2.tensor_total
        (fun k : ModeIndex => fullEigenprofile (α 0) k.2 k.1)
        (fullTensorFunction α')
        (fun k => coordinate_fullEigenprofile_memLp (α 0) k.2 k.1)
        (fullTensorFunction_memLp α')
        (fun f hf => coordinate_fullEigenprofile_total (α 0) f (fun odd n => hf (odd,n)))
        (fun f hf => by
          apply Lp.ext
          exact (ih α' (Lp.memLp f) hf).trans (Lp.coeFn_zero ℝ 2 (spatialMeasure α')).symm)
        hFp
      intro k l
      have he (p : ℝ×Space d) : fullTensorFunction α (Fin.cons k l) (e.symm p)=
          fullEigenprofile (α 0) k.2 k.1 p.1*fullTensorFunction α' l p.2 := by
        simp [fullTensorFunction,e,MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv,Fin.prod_univ_succ,α']
      have hh := h (Fin.cons k l)
      unfold spatialMeasure at hh
      rw [← hp.symm.integral_comp' (fun x => fullTensorFunction α (Fin.cons k l) x*F x)] at hh
      change (∫ p,fullTensorFunction α (Fin.cons k l) (e.symm p)*F (e.symm p)
        ∂(coordinateMeasure (α 0)).prod (spatialMeasure α'))=0 at hh
      simpa only [Function.comp_apply,he] using hh
    have hh := hp.quasiMeasurePreserving.ae hzero
    change ∀ᵐ x ∂spatialMeasure α,F x=0
    simpa only [spatialMeasure,e,Function.comp_apply,Pi.zero_apply,MeasurableEquiv.symm_apply_apply] using hh

theorem fullTensorFunction_total {d : ℕ} (α : MultiIndex d) (F : H α)
    (h : ∀ k : Fin d → ModeIndex,(∫ x,fullTensorFunction α k x*F x ∂spatialMeasure α)=0) : F=0 := by
  apply Lp.ext
  exact (fullTensorFunction_total_ae d α (Lp.memLp F) h).trans (Lp.coeFn_zero ℝ 2 (spatialMeasure α)).symm

#print axioms fullTensorFunction_total
end BecknerOnofri.Friedrichs.MixedSpatial
