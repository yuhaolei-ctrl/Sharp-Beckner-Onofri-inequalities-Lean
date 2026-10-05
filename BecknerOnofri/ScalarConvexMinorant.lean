import Mathlib.Analysis.Convex.Piecewise
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! The quartic-to-affine base used for the global convex scalar minorant.
Finite maxima with certified affine segments give a continuous convex
function and preserve the exact small-mean quartic. -/
noncomputable section
namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

def quarticBase (a e x : ℝ) : ℝ :=
  if x≤e then a*x^4 else a*e^4+4*a*e^3*(x-e)

theorem affine_convex (m c : ℝ) : ConvexOn ℝ univ (fun x : ℝ => m*x+c) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  have he : (u+v)*c=c := by rw [huv,one_mul]
  nlinarith [he]

theorem quartic_tangent_le (a e x : ℝ) (ha : 0≤a) :
    a*e^4+4*a*e^3*(x-e)≤a*x^4 := by
  have he : a*x^4-(a*e^4+4*a*e^3*(x-e))=
      a*(x-e)^2*((x+e)^2+2*e^2) := by ring
  have hn : 0≤a*(x-e)^2*((x+e)^2+2*e^2) := by positivity
  linarith

theorem quarticBase_continuous (a e : ℝ) : Continuous (quarticBase a e) := by
  have h : Continuous ((Iic e).piecewise (fun x : ℝ => a*x^4)
      (fun x => a*e^4+4*a*e^3*(x-e))) := by
    apply Continuous.piecewise ?_ (by fun_prop) (by fun_prop)
    intro x hx
    have hx' : x=e := by simpa only [frontier_Iic,mem_singleton_iff] using hx
    subst x
    ring
  exact h

theorem quarticBase_convex (a e : ℝ) (ha : 0≤a) : ConvexOn ℝ univ (quarticBase a e) := by
  let f : ℝ → ℝ := fun x => a*x^4-4*a*e^3*x
  let g : ℝ → ℝ := fun _ => -3*a*e^4
  have hp : ConvexOn ℝ univ (fun x : ℝ => a*x^4) := by
    simpa only [smul_eq_mul] using (show Even (4 : ℕ) by decide).convexOn_pow.smul ha
  have hf : ConvexOn ℝ (Iic e) f := by
    have h := hp.add (affine_convex (-4*a*e^3) 0)
    have he : (fun x => a*x^4)+ (fun x => (-4*a*e^3)*x+0)=f := by ext x; dsimp [f]; ring
    rw [he] at h
    exact h.subset (subset_univ _) (convex_Iic e)
  have hg : ConvexOn ℝ (Ici e) g := convexOn_const _ (convex_Ici e)
  have hderiv (x : ℝ) : HasDerivAt f (4*a*x^3-4*a*e^3) x := by
    convert! (((hasDerivAt_id x).pow 4).const_mul a).sub
      ((hasDerivAt_id x).const_mul (4*a*e^3)) using 1 <;> simp [f] <;> ring
  have hanti : AntitoneOn f (Iic e) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic e)
      (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
      (fun x _ => (hderiv x).hasDerivWithinAt)
    intro x hx
    have hx' : x≤e := by have := interior_subset hx; exact this
    have hpow : x^3≤e^3 := (show Odd (3 : ℕ) by decide).strictMono_pow.monotone hx'
    nlinarith [mul_le_mul_of_nonneg_left hpow ha]
  have hmono : MonotoneOn g (Ici e) := fun _ _ _ _ _ => le_rfl
  have heq : f e=g e := by dsimp [f,g]; ring
  have h := (convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici hf hg hanti hmono heq).add
    (affine_convex (4*a*e^3) 0)
  convert! h using 1
  ext x
  by_cases hx : x≤e <;> simp [quarticBase,f,g,hx,Set.piecewise] <;> ring

structure AffinePiece where
  slope : ℚ
  intercept : ℚ

def AffinePiece.value (p : AffinePiece) (x : ℝ) : ℝ := (p.slope : ℝ)*x+p.intercept

def convexMinorant (a e : ℝ) : List AffinePiece → ℝ → ℝ
  | [] => quarticBase a e
  | p::ps => fun x => max (p.value x) (convexMinorant a e ps x)

theorem convexMinorant_convex (a e : ℝ) (ha : 0≤a) (ps : List AffinePiece) :
    ConvexOn ℝ univ (convexMinorant a e ps) := by
  induction ps with
  | nil => exact quarticBase_convex a e ha
  | cons p ps ih => exact (affine_convex p.slope p.intercept).sup ih

theorem convexMinorant_continuous (a e : ℝ) (ps : List AffinePiece) :
    Continuous (convexMinorant a e ps) := by
  induction ps with
  | nil => exact quarticBase_continuous a e
  | cons p ps ih => exact (show Continuous p.value by unfold AffinePiece.value; fun_prop).max ih

theorem convexMinorant_small (a e : ℝ) (ha : 0≤a) (ps : List AffinePiece)
    (hp : ∀ p ∈ ps,4*a*e^3≤(p.slope : ℝ) ∧ p.value e≤a*e^4)
    (x : ℝ) (hx : x≤e) : convexMinorant a e ps x=a*x^4 := by
  induction ps with
  | nil => simp [convexMinorant,quarticBase,hx]
  | cons p ps ih =>
    have h := hp p (List.mem_cons_self ..)
    have hrest := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    change max (p.value x) (convexMinorant a e ps x)=a*x^4
    rw [hrest]
    apply max_eq_right
    have hm := mul_le_mul_of_nonpos_right h.1 (sub_nonpos.mpr hx)
    have ht := quartic_tangent_le a e x ha
    unfold AffinePiece.value at h ⊢
    nlinarith

#print axioms convexMinorant_convex
#print axioms convexMinorant_small
end BecknerOnofri.HighDim.ScalarCertificate
