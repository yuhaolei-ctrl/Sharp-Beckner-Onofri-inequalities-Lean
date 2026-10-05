import BecknerOnofri.SpinCandidateInterval

namespace BecknerOnofri.HighDim.Spin
open Set

def spinCellChainCheck {ψ : ℝ → ℝ} (a b : ℚ) : List (CertifiedSpinCell ψ) → Bool
  | [] => false
  | [c] => decide (c.left≤a ∧ b≤c.right)
  | c::d::cs => decide (c.left≤a) && spinCellChainCheck c.right b (d::cs)

theorem spinCellChain_sound {ψ : ℝ → ℝ} (cs : List (CertifiedSpinCell ψ))
    (a b : ℚ) (hc : spinCellChainCheck a b cs=true)
    (q : Count → ℝ) (t : ℝ) (hq : FeasibleAt t q) (ht : t∈Icc (a : ℝ) (b : ℝ)) :
    t^4/250≤functional q+12*ψ t := by
  induction cs generalizing a with
  | nil => simp [spinCellChainCheck] at hc
  | cons c cs ih =>
    cases cs with
    | nil =>
      have h := of_decide_eq_true hc
      exact c.sound q t hq ⟨(show (c.left : ℝ)≤a by exact_mod_cast h.1).trans ht.1,
        ht.2.trans (show (b : ℝ)≤c.right by exact_mod_cast h.2)⟩
    | cons d ds =>
      have h := Bool.and_eq_true_iff.mp hc
      have hl := of_decide_eq_true h.1
      by_cases hx : t≤(c.right : ℝ)
      · exact c.sound q t hq ⟨(show (c.left : ℝ)≤a by exact_mod_cast hl).trans ht.1,hx⟩
      · exact ih c.right h.2 ⟨(le_of_not_ge hx),ht.2⟩

noncomputable def spinCellOfChain (ψ : ℝ → ℝ) (a b : ℚ)
    (cs : List (CertifiedSpinCell ψ)) (hc : spinCellChainCheck a b cs=true) :
    CertifiedSpinCell ψ where
  left := a
  right := b
  sound := fun q t hq ht => spinCellChain_sound cs a b hc q t hq ht

#print axioms spinCellChain_sound
end BecknerOnofri.HighDim.Spin
