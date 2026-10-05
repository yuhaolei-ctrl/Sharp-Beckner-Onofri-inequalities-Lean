module

public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.EntropyScalarCertificate.Hull

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set CircleScalar CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def minorantGammaCheck (c : CertifiedGammaCell) (i : ℕ) : Bool :=
  let p := hullLine pieces i
  decide (i<pieces.length ∧ (1/16 : ℚ)≤c.left ∧ hullKnot knots i≤c.left ∧
    (i+1=pieces.length ∨ c.right≤hullKnot knots (i+1)) ∧
    p.slope*c.left+p.intercept≤c.lower ∧ p.slope*c.right+p.intercept≤c.lower)

theorem affine_le_of_endpoints (p : AffinePiece) {a b x U : ℝ}
    (hx : x∈Icc a b) (ha : p.value a≤U) (hb : p.value b≤U) : p.value x≤U := by
  unfold AffinePiece.value at *
  by_cases hs : (0 : ℝ)≤p.slope
  · linarith [mul_le_mul_of_nonneg_left hx.2 hs]
  · linarith [mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hs)]

structure CertifiedMinorantCell where
  left : ℚ
  right : ℚ
  sound : ∀ t : ℝ,t∈Icc (left : ℝ) (right : ℝ) → psi t≤gamma t

noncomputable def minorantCellOfGamma (c : CertifiedGammaCell) (i : ℕ)
    (hc : minorantGammaCheck c i=true) : CertifiedMinorantCell where
  left := c.left
  right := c.right
  sound := by
    obtain ⟨hi,he,hl,hr,hvl,hvr⟩ := of_decide_eq_true hc
    intro t ht
    have hE : (1/16 : ℝ)≤(c.left : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr he
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
    have hL : (hullKnot knots i : ℝ)≤c.left := by exact_mod_cast hl
    have hR : i+1=pieces.length ∨ t≤(hullKnot knots (i+1) : ℝ) := by
      rcases hr with hr|hr
      · exact Or.inl hr
      · exact Or.inr (ht.2.trans (by exact_mod_cast hr))
    have hp := psi_piece_upper i hi t (hE.trans ht.1) (hL.trans ht.1) hR
    have hleft : (hullLine pieces i).value (c.left : ℝ)≤c.lower := by
      have h := (Rat.cast_le (K := ℝ)).mpr hvl
      simpa only [AffinePiece.value,Rat.cast_add,Rat.cast_mul] using h
    have hright : (hullLine pieces i).value (c.right : ℝ)≤c.lower := by
      have h := (Rat.cast_le (K := ℝ)).mpr hvr
      simpa only [AffinePiece.value,Rat.cast_add,Rat.cast_mul] using h
    exact hp.trans ((affine_le_of_endpoints _ ht hleft hright).trans (c.sound t ht))

def minorantChainCheck (a b : ℚ) : List CertifiedMinorantCell → Bool
  | [] => false
  | [c] => decide (c.left≤a ∧ b≤c.right)
  | c::d::cs => decide (c.left≤a) && minorantChainCheck c.right b (d::cs)

theorem minorantChain_sound (cs : List CertifiedMinorantCell) (a b : ℚ)
    (hc : minorantChainCheck a b cs=true) (t : ℝ) (ht : t∈Icc (a : ℝ) (b : ℝ)) :
    psi t≤gamma t := by
  induction cs generalizing a with
  | nil => simp [minorantChainCheck] at hc
  | cons c cs ih =>
    cases cs with
    | nil =>
      have h := of_decide_eq_true hc
      exact c.sound t ⟨(show (c.left : ℝ)≤a by exact_mod_cast h.1).trans ht.1,
        ht.2.trans (show (b : ℝ)≤c.right by exact_mod_cast h.2)⟩
    | cons d ds =>
      have h := Bool.and_eq_true_iff.mp hc
      have hl := of_decide_eq_true h.1
      by_cases hx : t≤(c.right : ℝ)
      · exact c.sound t ⟨(show (c.left : ℝ)≤a by exact_mod_cast hl).trans ht.1,hx⟩
      · exact ih c.right h.2 ⟨le_of_not_ge hx,ht.2⟩

noncomputable def minorantCellOfChain (a b : ℚ) (cs : List CertifiedMinorantCell)
    (hc : minorantChainCheck a b cs=true) : CertifiedMinorantCell where
  left := a
  right := b
  sound := fun t ht => minorantChain_sound cs a b hc t ht

#print axioms minorantCellOfGamma
#print axioms minorantChain_sound
end BecknerOnofri.HighDim.ScalarCertificate
