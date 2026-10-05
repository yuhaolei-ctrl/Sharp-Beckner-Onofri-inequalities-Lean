import BecknerOnofri.WienerGraphGreen

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell
open LocalEleven.GraphRegularity LocalEleven.GraphWienerBounds

/-- Closed first-shell complement in the actual stronger Banach topology. -/
def complementSpace (d m : ℕ) : Submodule ℝ (graph d m) :=
  (ContinuousFirstShell.complement d).comap (toContinuous d m).toLinearMap

theorem complementSpace_closed (d m : ℕ) :
    IsClosed (complementSpace d m : Set (graph d m)) :=
  (complement_closed d).preimage (toContinuous d m).continuous

instance complementSpace_complete (d m : ℕ) : CompleteSpace (complementSpace d m) := by
  haveI : IsClosed (complementSpace d m : Set (graph d m)) := complementSpace_closed d m
  infer_instance

def toComplement (d m : ℕ) : complementSpace d m →L[ℝ] ContinuousFirstShell.complement d :=
  ((toContinuous d m).comp (complementSpace d m).subtypeL).codRestrict
    (ContinuousFirstShell.complement d) (fun x => x.property)

@[simp] lemma toComplement_val {d m : ℕ} (x : complementSpace d m) :
    (toComplement d m x).val=toContinuous d m x.val := rfl

lemma toComplement_injective (d m : ℕ) : Function.Injective (toComplement d m) := by
  intro x y h
  apply Subtype.ext
  apply toContinuous_injective d m
  exact congrArg Subtype.val h

def projectComplement (d m : ℕ) : graph d m →L[ℝ] complementSpace d m :=
  (projection d m).codRestrict (complementSpace d m) (fun x => by
    change toContinuous d m (projection d m x)∈ContinuousFirstShell.complement d
    rw [toContinuous_projection]
    exact (complementMap d (toContinuous d m x)).property)

@[simp] lemma toComplement_project {d m : ℕ} (x : graph d m) :
    toComplement d m (projectComplement d m x)=complementMap d (toContinuous d m x) := rfl

def firstShell (d m : ℕ) : Coordinates d →L[ℝ] graph d m :=
  LinearMap.mkContinuous
    { toFun := fun z => ofRadial (assembly d z) (radial_assembly m z)
      map_add' := fun x y => (toContinuous_injective d m) (by simp only [toContinuous_ofRadial,map_add])
      map_smul' := fun c x => (toContinuous_injective d m) (by
        simp only [toContinuous_ofRadial,map_smul,RingHom.id_apply]) }
    (2^(m+1)*d) (fun z => by
      change ‖ofRadial (assembly d z) (radial_assembly m z)‖≤(2^(m+1)*d)*‖z‖
      rw [norm_eq_wienerSize,toContinuous_ofRadial]
      exact wienerSize_assembly_le m z)

@[simp] lemma toContinuous_firstShell (d m : ℕ) (z : Coordinates d) :
    toContinuous d m (firstShell d m z)=assembly d z := rfl

def reconstruct (d m : ℕ) : Coordinates d × complementSpace d m →L[ℝ] graph d m :=
  (firstShell d m).comp (ContinuousLinearMap.fst ℝ _ _)+
    (complementSpace d m).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] lemma toContinuous_reconstruct {d m : ℕ} (x : Coordinates d × complementSpace d m) :
    toContinuous d m (reconstruct d m x)=assembly d x.1+(toComplement d m x.2).val := by
  change toContinuous d m (firstShell d m x.1+x.2.val)=_
  rw [map_add,toContinuous_firstShell]
  rfl

#print axioms complementSpace_closed
#print axioms toContinuous_reconstruct
end BecknerOnofri.HighDim.WienerGraph
