module

public import BecknerOnofri.ScalarMinorantAssembly

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate

/-- Local rational conditions for a continuous ordered family of affine
pieces. They suffice to locate its upper envelope without rechecking every
line at every mesh endpoint. -/
structure OrderedAffineHull (N : ℕ) where
  line : ℕ → AffinePiece
  knot : ℕ → ℚ
  knot_step : ∀ k,k<N → knot k≤knot (k+1)
  slope_step : ∀ k,k+1<N → (line k).slope≤(line (k+1)).slope
  join : ∀ k,k+1<N →
    (line k).slope*knot (k+1)+(line k).intercept=
      (line (k+1)).slope*knot (k+1)+(line (k+1)).intercept

theorem OrderedAffineHull.knots_mono {N : ℕ} (H : OrderedAffineHull N)
    {i j : ℕ} (hij : i≤j) (hj : j≤N) : H.knot i≤H.knot j := by
  induction j,hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (H.knot_step j (by omega))

theorem OrderedAffineHull.next_le {N : ℕ} (H : OrderedAffineHull N)
    (k : ℕ) (hk : k+1<N) (x : ℝ) (hx : x≤(H.knot (k+1) : ℝ)) :
    (H.line (k+1)).value x≤(H.line k).value x := by
  have hs : ((H.line k).slope : ℝ)≤(H.line (k+1)).slope := by exact_mod_cast H.slope_step k hk
  have he := congrArg (fun q : ℚ => (q : ℝ)) (H.join k hk)
  push_cast at he
  have hm := mul_le_mul_of_nonpos_right hs (sub_nonpos.mpr hx)
  unfold AffinePiece.value
  nlinarith

theorem OrderedAffineHull.le_next {N : ℕ} (H : OrderedAffineHull N)
    (k : ℕ) (hk : k+1<N) (x : ℝ) (hx : (H.knot (k+1) : ℝ)≤x) :
    (H.line k).value x≤(H.line (k+1)).value x := by
  have hs : ((H.line k).slope : ℝ)≤(H.line (k+1)).slope := by exact_mod_cast H.slope_step k hk
  have he := congrArg (fun q : ℚ => (q : ℝ)) (H.join k hk)
  push_cast at he
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx)
  unfold AffinePiece.value
  nlinarith

theorem OrderedAffineHull.prefix_le {N : ℕ} (H : OrderedAffineHull N)
    {i j : ℕ} (hij : i≤j) (hj : j<N) (x : ℝ) (hx : (H.knot j : ℝ)≤x) :
    (H.line i).value x≤(H.line j).value x := by
  induction j,hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have hm : (H.knot j : ℝ)≤H.knot (j+1) := by exact_mod_cast H.knot_step j (by omega)
    exact (ih (by omega) (hm.trans hx)).trans (H.le_next j hj x hx)

theorem OrderedAffineHull.suffix_le {N : ℕ} (H : OrderedAffineHull N)
    {i j : ℕ} (hij : i≤j) (hj : j<N) (x : ℝ) (hx : x≤(H.knot (i+1) : ℝ)) :
    (H.line j).value x≤(H.line i).value x := by
  induction j,hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have hm : (H.knot (i+1) : ℝ)≤H.knot (j+1) := by
      exact_mod_cast H.knots_mono (by omega : i+1≤j+1) (by omega)
    exact (H.next_le j hj x (hx.trans hm)).trans (ih (by omega))

theorem OrderedAffineHull.piece_dominates {N : ℕ} (H : OrderedAffineHull N)
    (i : ℕ) (hi : i<N) (x : ℝ)
    (hx : x∈Set.Icc (H.knot i : ℝ) (H.knot (i+1) : ℝ))
    (j : ℕ) (hj : j<N) : (H.line j).value x≤(H.line i).value x := by
  rcases le_total j i with h|h
  · exact H.prefix_le h hi x hx.1
  · exact H.suffix_le h hj x hx.2

#print axioms OrderedAffineHull.piece_dominates
end BecknerOnofri.HighDim.ScalarCertificate
