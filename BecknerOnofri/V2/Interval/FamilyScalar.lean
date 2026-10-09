module

public import BecknerOnofri.V2.Interval.ZeroJets
public import BecknerOnofri.V2.FiniteState.FamilyComparison

@[expose] public section

/-!
# The scalar bounds of Lemma `d12-spin-lem:scalar` for the FiniteState family

`family_scalar_bounds`: for `0 ≤ t ≤ 99/100`,
`t⁴/10 ≤ famF t` (strict for `t > 0`), `famResidVar t ≤ t⁴/50` (strict for `t > 0`) and
`-(1/4) ≤ famResid t j` for every state `j`, under the only hypotheses that the three finite
checks (`Row.checkCell` on all cells of the three rows) succeed.
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin

theorem famResidF_eq (t : ℝ) {j : ℕ} (hj : j < 13) : famResidF t j = famResid t ⟨j, hj⟩ := by
  simp [famResidF, hj]

/-- **Lemma `d12-spin-lem:scalar`** (eq. `d12-spin-eq:three`) for the explicit family: on
`0 ≤ t ≤ 99/100`, `f(t) ≥ t⁴/10`, `𝒱(t) ≤ t⁴/50` (both strict for `t > 0`) and `e_j(t) ≥ -1/4`.
The only hypotheses are the three finite computations `hc1 hc2 hc3`. -/
theorem family_scalar_bounds
    (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true) :
    ∀ t : ℝ, 0 ≤ t → t ≤ 99 / 100 →
      (t ^ 4 / 10 ≤ famF t ∧ (0 < t → t ^ 4 / 10 < famF t)) ∧
      (famResidVar t ≤ t ^ 4 / 50 ∧ (0 < t → famResidVar t < t ^ 4 / 50)) ∧
      ∀ j : Count, -(1 / 4 : ℝ) ≤ famResid t j := by
  obtain ⟨hzf, hzv⟩ := family_zero_jets hc1
  have key := scalar_certificate famF famResidVar (fun j t => famResidF t j) hc1 hc2 hc3 hzf hzv
    (fun t h0 h1 => (P1_registers h0 (by linarith)).1)
    (fun t h0 h1 => (P1_registers h0 (by linarith)).2.1)
    (fun t h0 h1 j hj => by
      show _ = famResidF t j + 1 / 4
      rw [(P1_registers h0 (by linarith)).2.2 j hj, famResidF_eq t hj])
    (fun t h0 h1 => (P2_registers (by linarith) (by linarith)).1)
    (fun t h0 h1 => (P2_registers (by linarith) (by linarith)).2.1)
    (fun t h0 h1 j hj => by
      show _ = famResidF t j + 1 / 4
      rw [(P2_registers (by linarith) (by linarith)).2.2 j hj, famResidF_eq t hj])
  intro t h0 h99
  obtain ⟨hF, hV, he⟩ := key t h0 h99
  refine ⟨hF, hV, fun j => ?_⟩
  have : -(1 / 4 : ℝ) ≤ famResidF t j.val := he j.val j.2
  rwa [famResidF_eq t j.2] at this

/-- Consumption by Lemma 5.20 (`family_variance_comparison`): its hypothesis
`∀ j, -(1/4) ≤ famResid t j` is exactly the third conclusion of `family_scalar_bounds`. -/
theorem family_variance_comparison_of_checks
    (hc1 : ∀ k < row1.count, row1.checkCell k = true)
    (hc2 : ∀ k < row2.count, row2.checkCell k = true)
    (hc3 : ∀ k < row3.count, row3.checkCell k = true)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 99 / 100) {q : Count → ℝ} (hq : FeasibleAt t q) :
    famF t - (30 / 7 : ℝ) * famResidVar t ≤ functional q + 12 * psiV2 t :=
  family_variance_comparison ht0 (by linarith) hq (family_scalar_bounds hc1 hc2 hc3 t ht0 ht1).2.2

end BecknerOnofri.V2.Interval
