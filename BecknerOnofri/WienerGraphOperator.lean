import BecknerOnofri.WienerGraphNorm

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell
open LocalEleven.GraphRegularity LocalEleven.GraphWienerBounds
open Legacy.BecknerOnofri.RadialWiener

lemma operator_radial {d m : ℕ} (L : Space d →L[ℝ] Space d)
    (hb : ∀ u k, ‖coefficient k (L u)‖≤‖coefficient k u‖)
    (u : Space d) (hu : Radial m u) : Radial m (L u) := by
  apply hu.of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  intro k
  exact mul_le_mul_of_nonneg_left (hb u k) ((radialWeight_isWeight m).nonneg k)

lemma operator_wienerSize_le {d m : ℕ} (L : Space d →L[ℝ] Space d)
    (hb : ∀ u k, ‖coefficient k (L u)‖≤‖coefficient k u‖)
    (u : Space d) (hu : Radial m u) : wienerSize m (L u)≤wienerSize m u := by
  apply (operator_radial L hb u hu).tsum_le_tsum _ hu
  intro k
  exact mul_le_mul_of_nonneg_left (hb u k) ((radialWeight_isWeight m).nonneg k)

/-- A Fourier multiplier contraction lifts to the complete weighted space,
with its original continuous function unchanged. -/
def liftContraction {d : ℕ} (m : ℕ) (L : Space d →L[ℝ] Space d)
    (hb : ∀ u k, ‖coefficient k (L u)‖≤‖coefficient k u‖) :
    graph d m →L[ℝ] graph d m :=
  LinearMap.mkContinuous
    { toFun := fun x => ofRadial (L (toContinuous d m x))
        (operator_radial L hb _ (toContinuous_radial x))
      map_add' := fun x y => (toContinuous_injective d m) (by simp only [toContinuous_ofRadial,map_add])
      map_smul' := fun c x => (toContinuous_injective d m) (by simp only [toContinuous_ofRadial,map_smul,RingHom.id_apply]) }
    1 (fun x => by
      change ‖ofRadial (L (toContinuous d m x)) (operator_radial L hb _ (toContinuous_radial x))‖≤1*‖x‖
      rw [one_mul,norm_eq_wienerSize,norm_eq_wienerSize,toContinuous_ofRadial]
      exact operator_wienerSize_le L hb _ (toContinuous_radial x))

@[simp] theorem toContinuous_liftContraction {d : ℕ} (m : ℕ) (L : Space d →L[ℝ] Space d)
    (hb : ∀ u k, ‖coefficient k (L u)‖≤‖coefficient k u‖) (x : graph d m) :
    toContinuous d m (liftContraction m L hb x)=L (toContinuous d m x) := rfl

#print axioms toContinuous_liftContraction
end BecknerOnofri.HighDim.WienerGraph
