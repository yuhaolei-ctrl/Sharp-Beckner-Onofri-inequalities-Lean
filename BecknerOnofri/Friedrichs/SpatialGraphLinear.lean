module

public import BecknerOnofri.Friedrichs.SpatialGraphClosed

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
namespace BecknerOnofri.Friedrichs.SpatialForm

lemma liftedGraph_zero (m : ℕ) : liftedGraph m 0 0 := by
  refine ⟨(closedFormSubmodule m).zero_mem,?_⟩
  intro w hw
  simp [formPairing]

lemma liftedGraph_add {m : ℕ} {u v : EnergySpace} {g h : H}
    (hu : liftedGraph m u g) (hv : liftedGraph m v h) : liftedGraph m (u+v) (g+h) := by
  refine ⟨(closedFormSubmodule m).add_mem hu.1 hv.1,?_⟩
  intro w hw
  have h1 := hu.2 w hw
  have h2 := hv.2 w hw
  dsimp [formPairing] at *
  simp only [Prod.fst_add,Prod.snd_add,inner_add_left]
  linarith

lemma liftedGraph_smul {m : ℕ} {u : EnergySpace} {g : H}
    (hu : liftedGraph m u g) (c : ℝ) : liftedGraph m (c • u) (c • g) := by
  refine ⟨(closedFormSubmodule m).smul_mem c hu.1,?_⟩
  intro w hw
  have h1 := hu.2 w hw
  dsimp [formPairing] at *
  simp only [Prod.fst_smul,Prod.snd_smul,inner_smul_left,conj_trivial]
  linear_combination c*h1

lemma operatorGraph_zero (m : ℕ) : operatorGraph m 0 0 := by
  apply (operatorGraph_iff_closed_tests m 0 0).mpr
  exact ⟨0,0,(liftedGraph_zero m).1,(liftedGraph_zero m).2⟩

lemma operatorGraph_add {m : ℕ} {f g h k : H}
    (hfg : operatorGraph m f g) (hhk : operatorGraph m h k) : operatorGraph m (f+h) (g+k) := by
  obtain ⟨p,v,hc,ht⟩ := (operatorGraph_iff_closed_tests m f g).mp hfg
  obtain ⟨q,w,hc',ht'⟩ := (operatorGraph_iff_closed_tests m h k).mp hhk
  have he := liftedGraph_add (show liftedGraph m (f,(p,v)) g from ⟨hc,ht⟩)
    (show liftedGraph m (h,(q,w)) k from ⟨hc',ht'⟩)
  exact (operatorGraph_iff_closed_tests m (f+h) (g+k)).mpr ⟨p+q,v+w,he.1,he.2⟩

lemma operatorGraph_smul {m : ℕ} {f g : H} (hfg : operatorGraph m f g) (c : ℝ) :
    operatorGraph m (c • f) (c • g) := by
  obtain ⟨p,v,hc,ht⟩ := (operatorGraph_iff_closed_tests m f g).mp hfg
  have he := liftedGraph_smul (show liftedGraph m (f,(p,v)) g from ⟨hc,ht⟩) c
  exact (operatorGraph_iff_closed_tests m (c • f) (c • g)).mpr ⟨c • p,c • v,he.1,he.2⟩

lemma operatorGraph_sum {ι : Type*} (m : ℕ) (S : Finset ι) (f g : ι → H)
    (h : ∀ i∈S,operatorGraph m (f i) (g i)) :
    operatorGraph m (∑ i∈S,f i) (∑ i∈S,g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using operatorGraph_zero m
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact operatorGraph_add (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

#print axioms operatorGraph_sum
end BecknerOnofri.Friedrichs.SpatialForm
