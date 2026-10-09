module

public import BecknerOnofri.V2.Eleven.SymbolClass
public import BecknerOnofri.ElevenPeriodizedSummability

@[expose] public section

/-! # `eq:section4-profile-derivative-decay`: derivative decay of `η_{1/5}` and the M-test majorants

Lemma 4.3 (`lem:section4-periodization-entropy-identity`), proof, first display:
`|∂^α η_{1/5}(x)| ≤ C_α (1+|x|)^{-22-|α|}`, and `eq:section4-periodization-M-test`:
`∑_{n ∈ ℤ^{11}} sup_{y ∈ K} |∂^α η_{1/5}(y+n)| < ∞` for compact `K`.

Here `η_{1/5}` is the repository's `Eleven.euclideanProfile`
(`x ↦ 5^{11} · (122880/π^6) · (1 + 25 |x|²)^{-11}`), `‖·‖` is the supremum norm of `Fin 11 → ℝ`
(equivalent to the Euclidean norm up to constants, so the decay statement is unchanged), and the
derivative of order `k` is `iteratedFDeriv ℝ k` (the family of all `∂^α`, `|α| = k`). -/

noncomputable section
open scoped ContDiff
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Eleven
open Legacy.TorusEndpoint.GreenMultiplierSummability

namespace BecknerOnofri.V2.Eleven

/-- `x ↦ 1 + 25 |x|²`. -/
def quad11 (x : Fin 11 → ℝ) : ℝ := 1 + 25 * ∑ i, x i ^ 2

lemma quad11_isSym : IsSym 2 quad11 := by
  have hcoord (i : Fin 11) : IsSym 1 (fun x : Fin 11 → ℝ => x i) :=
    IsSym.clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 11 => ℝ) i)
  have hsq (i : Fin 11) : IsSym 2 (fun x : Fin 11 → ℝ => x i ^ 2) := by
    have := (hcoord i).pow 2
    simpa using this
  have hsum : IsSym 2 (fun x : Fin 11 → ℝ => ∑ i, x i ^ 2) :=
    IsSym.finset_sum _ (by norm_num) fun i _ => hsq i
  have h25 := hsum.const_smul 25
  have h1 : IsSym 2 (fun _ : Fin 11 → ℝ => (1 : ℝ)) := (IsSym.const (1 : ℝ)).mono (by norm_num)
  have e : quad11 = fun x : Fin 11 → ℝ =>
      (fun _ : Fin 11 → ℝ => (1 : ℝ)) x + (25 : ℝ) • (fun x : Fin 11 → ℝ => ∑ i, x i ^ 2) x := by
    funext x; simp [quad11]
  rw [e]
  exact h1.add h25

lemma quad11_lower (x : Fin 11 → ℝ) : (1 / 2 : ℝ) * (1 + ‖x‖) ^ (2 : ℤ) ≤ quad11 x := by
  have hn : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, ‖x‖ = |x i| := by
      by_cases h : (Finset.univ : Finset (Fin 11)).Nonempty
      · obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) h
        refine ⟨i, le_antisymm ?_ ?_⟩
        · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ j)
        · simpa using norm_le_pi_norm x i
      · exact absurd ⟨(0 : Fin 11), Finset.mem_univ _⟩ h
    rw [hi, sq_abs]
    exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hx0 := norm_nonneg x
  unfold quad11
  rw [zpow_ofNat]
  nlinarith [sq_nonneg (‖x‖ - 1), Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i))]

lemma invQuad11_isSym : IsSym (-2) (fun x => (quad11 x)⁻¹) :=
  quad11_isSym.inv (c := 1 / 2) (by norm_num) quad11_lower

/-- `η_{1/5} ∈ S^{-22}`. -/
lemma euclideanProfile_isSym : IsSym (-22) euclideanProfile := by
  have h := (invQuad11_isSym.pow 11).const_smul ((5 : ℝ) ^ 11 * (122880 / Real.pi ^ 6))
  have e : euclideanProfile = fun x => ((5 : ℝ) ^ 11 * (122880 / Real.pi ^ 6)) • ((quad11 x)⁻¹) ^ 11 := by
    funext x
    simp only [euclideanProfile, quad11, smul_eq_mul]
    rw [zpow_neg, zpow_ofNat, inv_pow]
  rw [e]
  refine h.mono (le_of_eq ?_)
  norm_num

/-- `eq:section4-profile-derivative-decay`: `‖D^k η_{1/5}(x)‖ ≤ C_k (1+‖x‖)^{-22-k}`. -/
theorem profile_derivative_decay (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin 11 → ℝ,
      ‖iteratedFDeriv ℝ k euclideanProfile x‖ ≤ C * (1 + ‖x‖) ^ (-22 - (k : ℤ)) := by
  obtain ⟨C, hC⟩ := euclideanProfile_isSym.2 k k le_rfl
  refine ⟨C, ?_, hC⟩
  have := (norm_nonneg _).trans (hC 0)
  simpa using this

theorem profile_contDiff : ContDiff ℝ ∞ euclideanProfile := euclideanProfile_isSym.1

end BecknerOnofri.V2.Eleven
