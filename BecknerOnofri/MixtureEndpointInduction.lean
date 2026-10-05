import BecknerOnofri.MixtureMarginals

/-! The high-dimensional endpoint induction. Its sole dimension-specific input
is the exact twelve-dimensional cosine-mixture endpoint. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open Finset

namespace BecknerOnofri.CosineMixtureTransfer
open Legacy.TorusEndpoint Legacy.BecknerOnofri

/-- The precise endpoint on positive countable correlated cosine mixtures. -/
def MixtureEndpoint (d : ℕ) : Prop :=
  ∀ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ),
    (∀ n, 0 ≤ w n) → HasSum w 1 →
    Summable (fun n => w n * CosineMixture.tensor (N n) 0) →
    (∀ x, 0 < CosineMixtureApproximation.rho w N x) →
    energy (d:ℝ) (CosineMixtureApproximation.rho w N) ≤
      2 * densityEntropy (CosineMixtureApproximation.rho w N)

theorem mixture_endpoint_successor {d : ℕ} (hd : 12 ≤ d) (hE : MixtureEndpoint d) :
    MixtureEndpoint (d+1) := by
  intro w N hw hm hSup hpos
  have hdim := countable_mixture_dimension_transfer hd w N hw hm.summable hSup
  have hMarg (i : Fin (d+1)) := hE w (fun n => drop i (N n)) hw hm
    (summable_drop_majorant i w N hw hSup) (rho_drop_pos i w N hw hSup hpos)
  have hent := mixture_entropy_deletion_le w N hw hm hSup hpos
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  calc
    _ ≤ (1/(d:ℝ)) * ∑ i : Fin (d+1),
        energy (d:ℝ) (CosineMixtureApproximation.rho w (fun n => drop i (N n))) := hdim
    _ ≤ (1/(d:ℝ)) * ∑ i : Fin (d+1),
        2 * densityEntropy (CosineMixtureApproximation.rho w (fun n => drop i (N n))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hMarg i)) (by positivity)
    _ = (1/(d:ℝ)) * (2 * ∑ i : Fin (d+1),
        densityEntropy (CosineMixtureApproximation.rho w (fun n => drop i (N n)))) := by simp only [mul_sum]
    _ ≤ (1/(d:ℝ)) * (2 * ((d:ℝ) * densityEntropy (CosineMixtureApproximation.rho w N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hent (by norm_num)) (by positivity)
    _ = _ := by field_simp

/-- No positivity, spectral-slice, rectangle, representation, or entropy
comparison assumptions remain in the induction step. Only d=12 is a premise. -/
theorem mixture_endpoint_from_twelve (h12 : MixtureEndpoint 12) {d : ℕ} (hd : 12 ≤ d) :
    MixtureEndpoint d := by
  induction d, hd using Nat.le_induction with
  | base => exact h12
  | succ d hd ih => exact mixture_endpoint_successor hd ih

#print axioms mixture_endpoint_from_twelve

end BecknerOnofri.CosineMixtureTransfer
