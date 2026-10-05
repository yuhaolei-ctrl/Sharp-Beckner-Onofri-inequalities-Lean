import BecknerOnofri.Friedrichs.FormLift

/-! Continuity extends the weak equation from compactly supported smooth tests
to every element of the spatial form closure. -/
noncomputable section
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.SpatialForm

def formPairing (u w : EnergySpace) : ℝ :=
  inner ℝ u.2.1 w.2.1+inner ℝ u.2.2 w.2.2

lemma formPairing_continuous_right (u : EnergySpace) : Continuous (formPairing u) := by
  unfold formPairing
  exact (continuous_const.inner (continuous_fst.comp continuous_snd)).add
    (continuous_const.inner (continuous_snd.comp continuous_snd))

lemma formPairing_comm (u w : EnergySpace) : formPairing u w=formPairing w u := by
  simp only [formPairing,real_inner_comm]

lemma core_test_extends {m : ℕ} {u : EnergySpace} {g : H}
    (h : ∀ w∈core m,formPairing u w=inner ℝ g w.1) :
    ∀ w∈formClosure m,formPairing u w=inner ℝ g w.1 := by
  intro w hw
  exact closure_minimal h
    (isClosed_eq (formPairing_continuous_right u) (continuous_const.inner continuous_fst)) hw

lemma operatorGraph_iff_closed_tests (m : ℕ) (f g : H) :
    operatorGraph m f g ↔ ∃ p v : H,(f,(p,v))∈formClosure m ∧
      ∀ w∈formClosure m,formPairing (f,(p,v)) w=inner ℝ g w.1 := by
  constructor
  · rintro ⟨p,v,hc,ht⟩
    exact ⟨p,v,hc,core_test_extends ht⟩
  · rintro ⟨p,v,hc,ht⟩
    exact ⟨p,v,hc,fun w hw => ht w (subset_closure hw)⟩

lemma operatorGraph_energy {m : ℕ} {f g : H} (h : operatorGraph m f g) :
    ∃ p v : H,(f,(p,v))∈formClosure m ∧ ‖p‖^2+‖v‖^2=inner ℝ g f := by
  obtain ⟨p,v,hc,ht⟩ := (operatorGraph_iff_closed_tests m f g).mp h
  refine ⟨p,v,hc,?_⟩
  simpa only [formPairing,real_inner_self_eq_norm_sq] using ht _ hc

#print axioms core_test_extends
end BecknerOnofri.Friedrichs.SpatialForm
