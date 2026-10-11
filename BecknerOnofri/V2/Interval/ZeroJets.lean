module

public import BecknerOnofri.V2.Interval.FamilyBridge
public import BecknerOnofri.V2.FiniteState.OriginVanishing
public import BecknerOnofri.V2.Reaudit.ScalarBridges.OriginBridge

@[expose] public section

/-!
# The zero-jet hypotheses of the scalar certificate

If `A` is a coherent jet on a set `S` with unique differentiability, then the `n`-th coefficient
of `A x` is `(n!)⁻¹` times the `n`-th derivative within `S` of the zeroth coefficient.  Applied to
the chains of `f` and `𝒱` of the first row on `[0, 1/8]`, whose zeroth coefficients are `famF` and
`famResidVar` (`P1_registers`), the vanishing of the first four derivatives at `0`
gives `hzf` and `hzv`.  The vanishings are taken from the printed origin summary
`ScalarBridges.origin_summary_printed` (`eq:section5-origin-summary`: analyticity at `0`,
`e_j = O(t³)`, `𝒱 = O(t⁶)`, `f = O(t⁴)`, hence `f^{(k)}(0) = 𝒱^{(k)}(0) = 0` for `k ≤ 3`).
-/

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset BecknerOnofri.V2.FiniteState

theorem Coh.iteratedDerivWithin_coeff {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} (hA : Coh S A)
    (hS : UniqueDiffOn ℝ S) (n : ℕ) :
    Set.EqOn (iteratedDerivWithin n (fun s => coeff 0 (A s)) S)
      (fun y => (n.factorial : ℝ) * coeff n (A y)) S := by
  induction n with
  | zero =>
    intro x hx
    simp [iteratedDerivWithin_zero]
  | succ n ih =>
    intro x hx
    rw [iteratedDerivWithin_succ]
    have h1 : derivWithin (iteratedDerivWithin n (fun s => coeff 0 (A s)) S) S x =
        derivWithin (fun y => (n.factorial : ℝ) * coeff n (A y)) S x :=
      derivWithin_congr ih (ih hx)
    rw [h1]
    have h2 : HasDerivAt (fun y => (n.factorial : ℝ) * coeff n (A y))
        ((n.factorial : ℝ) * coeff n (d⁄dX (A x))) x :=
      (hA x hx n).const_mul _
    rw [h2.hasDerivWithinAt.derivWithin (hS x hx), coeff_derivative, Nat.factorial_succ]
    push_cast
    ring

theorem Coh.coeff_eq_zero {S : Set ℝ} {A : ℝ → ℝ⟦X⟧} {F : ℝ → ℝ} {x : ℝ} (hA : Coh S A)
    (hS : UniqueDiffOn ℝ S) (hx : x ∈ S) (hAF : ∀ s ∈ S, coeff 0 (A s) = F s)
    {n : ℕ} (hF : ContDiffAt ℝ n F x) (hz : iteratedDeriv n F x = 0) : coeff n (A x) = 0 := by
  have h1 := hA.iteratedDerivWithin_coeff hS n hx
  have h2 : iteratedDerivWithin n (fun s => coeff 0 (A s)) S x = iteratedDerivWithin n F S x :=
    iteratedDerivWithin_congr (fun s hs => hAF s hs) hx
  have h3 : iteratedDerivWithin n F S x = iteratedDeriv n F x :=
    iteratedDerivWithin_eq_iteratedDeriv hS hF hx
  rw [h2, h3, hz] at h1
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  exact (mul_eq_zero.1 h1.symm).resolve_left hn

end BecknerOnofri.V2.Interval

namespace BecknerOnofri.V2.Interval

open PowerSeries Finset BecknerOnofri.V2.FiniteState

/-- The zero-jet hypotheses `hzf`, `hzv` of `scalar_certificate`, from the origin vanishings of
`famF` and `famResidVar`, given the first-row cell checks (which provide the coherence of the
chains on `[0, 1/8]`). -/
theorem family_zero_jets (hc1 : ∀ k < row1.count, row1.checkCell k = true) :
    (∀ n < 4, coeff n (chain P1.1 P1.2.f 0) = 0) ∧ (∀ n < 4, coeff n (chain P1.1 P1.2.v 0) = 0) := by
  obtain ⟨⟨cf, _⟩, ⟨cv, _⟩, _⟩ :=
    Row.small_pointwise row1_valid (by decide) row1_small (by decide) (by decide) (by decide) hc1
  have ha : ((row1.aN : ℤ) : ℝ) / (row1.aD : ℝ) = 0 := by norm_num [row1]
  have hb : ((row1.bN : ℤ) : ℝ) / (row1.bD : ℝ) = 1 / 8 := by norm_num [row1]
  rw [ha, hb] at cf cv
  have cf' : Coh (Set.Icc (0 : ℝ) (1 / 8)) (chain P1.1 P1.2.f) := cf
  have cv' : Coh (Set.Icc (0 : ℝ) (1 / 8)) (chain P1.1 P1.2.v) := cv
  have hS : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) (1 / 8)) := uniqueDiffOn_Icc (by norm_num)
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 8) := ⟨le_rfl, by norm_num⟩
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 8), coeff 0 (chain P1.1 P1.2.f s) = famF s := fun s hs =>
    (regVal_eq_coeff0 P1.1 P1.2.f s).symm.trans
      (P1_registers hs.1 (lt_of_le_of_lt hs.2 (by norm_num))).1
  have hv : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 8), coeff 0 (chain P1.1 P1.2.v s) = famResidVar s :=
    fun s hs => (regVal_eq_coeff0 P1.1 P1.2.v s).symm.trans
      (P1_registers hs.1 (lt_of_le_of_lt hs.2 (by norm_num))).2.1
  obtain ⟨_, _, hvan⟩ := Reaudit.ScalarBridges.origin_summary_printed
  have f0 : iteratedDeriv 0 famF 0 = 0 := hvan.1 0 (by norm_num)
  have f1 : iteratedDeriv 1 famF 0 = 0 := hvan.1 1 (by norm_num)
  have f2 : iteratedDeriv 2 famF 0 = 0 := hvan.1 2 (by norm_num)
  have f3 : iteratedDeriv 3 famF 0 = 0 := hvan.1 3 (by norm_num)
  have v0 : iteratedDeriv 0 famResidVar 0 = 0 := hvan.2 0 (by norm_num)
  have v1 : iteratedDeriv 1 famResidVar 0 = 0 := hvan.2 1 (by norm_num)
  have v2 : iteratedDeriv 2 famResidVar 0 = 0 := hvan.2 2 (by norm_num)
  have v3 : iteratedDeriv 3 famResidVar 0 = 0 := hvan.2 3 (by norm_num)
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · interval_cases n
    · exact cf'.coeff_eq_zero hS h0 hf (famF_contDiffAt _) f0
    · exact cf'.coeff_eq_zero hS h0 hf (famF_contDiffAt _) f1
    · exact cf'.coeff_eq_zero hS h0 hf (famF_contDiffAt _) f2
    · exact cf'.coeff_eq_zero hS h0 hf (famF_contDiffAt _) f3
  · interval_cases n
    · exact cv'.coeff_eq_zero hS h0 hv (famResidVar_contDiffAt _) v0
    · exact cv'.coeff_eq_zero hS h0 hv (famResidVar_contDiffAt _) v1
    · exact cv'.coeff_eq_zero hS h0 hv (famResidVar_contDiffAt _) v2
    · exact cv'.coeff_eq_zero hS h0 hv (famResidVar_contDiffAt _) v3

end BecknerOnofri.V2.Interval
