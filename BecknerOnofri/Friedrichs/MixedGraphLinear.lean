import BecknerOnofri.Friedrichs.MixedFormSubmodule
import BecknerOnofri.Friedrichs.MixedClosedFormTests

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma formPairing_comm {d : ℕ} {α : MultiIndex d} (v w : EnergySpace α) :
    formPairing v w=formPairing w v := by simp only [formPairing,real_inner_comm]

lemma formPairing_add_left {d : ℕ} {α : MultiIndex d} (u v w : EnergySpace α) :
    formPairing (u+v) w=formPairing u w+formPairing v w := by
  simp only [formPairing,Prod.fst_add,Prod.snd_add,Pi.add_apply,inner_add_left]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma formPairing_smul_left {d : ℕ} {α : MultiIndex d} (c : ℝ) (u w : EnergySpace α) :
    formPairing (c • u) w=c*formPairing u w := by
  change (∑ i,(inner ℝ (c • u.2.1 i) (w.2.1 i)+inner ℝ (c • u.2.2 i) (w.2.2 i)))=_
  simp only [formPairing,real_inner_smul_left,mul_add,Finset.mul_sum]

lemma operatorGraph_zero {d : ℕ} (α : MultiIndex d) : operatorGraph α 0 0 := by
  refine ⟨0,rfl,(closedFormSubmodule α).zero_mem,?_⟩
  intro w hw
  simp [formPairing]

lemma operatorGraph_add {d : ℕ} {α : MultiIndex d} {f g h k : H α}
    (hfg : operatorGraph α f g) (hhk : operatorGraph α h k) : operatorGraph α (f+h) (g+k) := by
  obtain ⟨u,rfl,hu,ht⟩ := hfg
  obtain ⟨v,rfl,hv,hs⟩ := hhk
  refine ⟨u+v,rfl,(closedFormSubmodule α).add_mem hu hv,?_⟩
  intro w hw
  rw [formPairing_add_left,ht w hw,hs w hw,inner_add_left]

lemma operatorGraph_smul {d : ℕ} {α : MultiIndex d} {f g : H α}
    (hfg : operatorGraph α f g) (c : ℝ) : operatorGraph α (c • f) (c • g) := by
  obtain ⟨u,rfl,hu,ht⟩ := hfg
  refine ⟨c • u,rfl,(closedFormSubmodule α).smul_mem c hu,?_⟩
  intro w hw
  rw [formPairing_smul_left,ht w hw,real_inner_smul_left]

lemma operatorGraph_sum {d : ℕ} {α : MultiIndex d} {ι : Type*} (s : Finset ι)
    (f g : ι → H α) (h : ∀ i∈s,operatorGraph α (f i) (g i)) :
    operatorGraph α (∑ i∈s,f i) (∑ i∈s,g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using operatorGraph_zero α
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact operatorGraph_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma operatorGraph_symmetric {d : ℕ} {α : MultiIndex d} {f g h k : H α}
    (hfg : operatorGraph α f g) (hhk : operatorGraph α h k) : inner ℝ g h=inner ℝ f k := by
  obtain ⟨u,rfl,hu,ht⟩ := hfg
  obtain ⟨v,rfl,hv,hs⟩ := hhk
  rw [← ht v hv,formPairing_comm,hs u hu,real_inner_comm]

#print axioms operatorGraph_sum
#print axioms operatorGraph_symmetric
end BecknerOnofri.Friedrichs.MixedSpatial
