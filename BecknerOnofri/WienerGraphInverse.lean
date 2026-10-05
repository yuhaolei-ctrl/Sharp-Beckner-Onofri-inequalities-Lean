import BecknerOnofri.WienerGraphComplement

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell

-- Pin the inherited additive instances: otherwise elaborating endomorphism
-- subtraction explores unrelated ring structures of the nested subspaces.
local instance (d m : ℕ) : AddCommGroup (graph d m) :=
  (inferInstance : NormedAddCommGroup (graph d m)).toAddCommGroup
local instance (d m : ℕ) : AddCommGroup (complementSpace d m) :=
  (inferInstance : NormedAddCommGroup (complementSpace d m)).toAddCommGroup

private abbrev continuousEquiv {d : ℕ} (hd : 11≤d) :=
  LocalEleven.continuousComplementContinuousLinearEquiv hd
    (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)≤2)

lemma continuousEquiv_apply {d : ℕ} (hd : 11≤d) (u : complement d) :
    continuousEquiv hd u=u-continuousComplementGreen (by omega) u := by
  have h := congrArg (fun L : complement d →L[ℝ] complement d => L u)
    (LocalEleven.continuousComplementContinuousLinearEquiv_one hd)
  exact h

lemma continuous_inverse_as_sum {d : ℕ} (hd : 11≤d) (u : complement d) :
    (continuousEquiv hd).symm u=u+LocalEleven.QuadraticSlaving.inverseGreen hd u.val := by
  have hG : complementMap d (greenContinuous d u.val)=continuousComplementGreen (by omega) u := by
    exact complementMap_subtype (continuousComplementGreen (by omega) u)
  have hH : LocalEleven.QuadraticSlaving.inverseGreen hd u.val=
      (continuousEquiv hd).symm (continuousComplementGreen (by omega) u) := by
    change (continuousEquiv hd).symm (complementMap d (greenContinuous d u.val))=_
    rw [hG]
  rw [hH]
  apply (continuousEquiv hd).injective
  rw [map_add,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,
    continuousEquiv_apply]
  abel

def greenComplement {d : ℕ} (hd : 0<d) (m : ℕ) : complementSpace d m →L[ℝ] complementSpace d m :=
  ((green hd m).comp (complementSpace d m).subtypeL).codRestrict (complementSpace d m)
    (fun x => by
      change toContinuous d m (green hd m x.val)∈complement d
      rw [toContinuous_green]
      exact greenContinuous_mem_complement hd (toComplement d m x))

def inverseCorrection {d : ℕ} (hd : 11≤d) (m : ℕ) :
    complementSpace d m →L[ℝ] complementSpace d m :=
  ((slavingInverse hd m).comp (complementSpace d m).subtypeL).codRestrict (complementSpace d m)
    (fun x => by
      change toContinuous d m (slavingInverse hd m x.val)∈complement d
      rw [toContinuous_slavingInverse]
      exact (LocalEleven.QuadraticSlaving.inverseGreen hd (toContinuous d m x.val)).property)

def forward {d : ℕ} (hd : 11≤d) (m : ℕ) : complementSpace d m →L[ℝ] complementSpace d m :=
  (ContinuousLinearMap.id ℝ (complementSpace d m) - greenComplement (d := d) (by omega) m : complementSpace d m →L[ℝ] complementSpace d m)

def inverse {d : ℕ} (hd : 11≤d) (m : ℕ) : complementSpace d m →L[ℝ] complementSpace d m :=
  (ContinuousLinearMap.id ℝ (complementSpace d m) + inverseCorrection hd m : complementSpace d m →L[ℝ] complementSpace d m)

lemma toComplement_forward {d : ℕ} (hd : 11≤d) (m : ℕ) (x : complementSpace d m) :
    toComplement d m (forward hd m x)=continuousEquiv hd (toComplement d m x) := by
  rw [continuousEquiv_apply]
  apply Subtype.ext
  change toContinuous d m (x.val-green (by omega) m x.val)=_
  rw [map_sub,toContinuous_green]
  rfl

lemma toComplement_inverse {d : ℕ} (hd : 11≤d) (m : ℕ) (x : complementSpace d m) :
    toComplement d m (inverse hd m x)=(continuousEquiv hd).symm (toComplement d m x) := by
  rw [continuous_inverse_as_sum]
  apply Subtype.ext
  change toContinuous d m (x.val+slavingInverse hd m x.val)=_
  rw [map_add,toContinuous_slavingInverse]
  rfl

/-- The actual I−G inverse is bounded on each complete weighted complement. -/
def complementEquiv {d : ℕ} (hd : 11≤d) (m : ℕ) : complementSpace d m ≃L[ℝ] complementSpace d m where
  toLinearEquiv :=
    { toFun := forward hd m
      invFun := inverse hd m
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun x => (toComplement_injective d m) (by
        rw [toComplement_inverse,toComplement_forward,ContinuousLinearEquiv.symm_apply_apply])
      right_inv := fun x => (toComplement_injective d m) (by
        rw [toComplement_forward,toComplement_inverse,ContinuousLinearEquiv.apply_symm_apply]) }
  continuous_toFun := (forward hd m).continuous
  continuous_invFun := (inverse hd m).continuous

lemma complementEquiv_toCLM {d : ℕ} (hd : 11≤d) (m : ℕ) :
    (complementEquiv hd m).toContinuousLinearMap=
      (ContinuousLinearMap.id ℝ (complementSpace d m) - greenComplement (d := d) (by omega) m : complementSpace d m →L[ℝ] complementSpace d m) := rfl

#print axioms complementEquiv_toCLM
end BecknerOnofri.HighDim.WienerGraph
