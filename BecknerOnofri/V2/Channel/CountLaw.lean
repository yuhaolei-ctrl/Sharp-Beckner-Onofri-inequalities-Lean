module

public import BecknerOnofri.SpinCountMoments
public import BecknerOnofri.SpinChannelMean
public import BecknerOnofri.V2.Circle.Psi
public import BecknerOnofri.V2.FiniteState.FamilyDefs

@[expose] public section

/-!
# The count law on `Fin 13` (work package G10, part (a))

Source: the count-law identities at the beginning of the subsection "The finite-state entropy
inequality" (`eq:section5-spin-count-probabilities`, `eq:section5-spin-count-identities`) and the
converse sentence "each `p ∈ 𝒫_t` is the count vector of the exchangeable probability measure
with common spin mean `t` that assigns probability `p_j / C(12,j)` to each configuration containing
exactly `j` positive spins".

A configuration is the finset of its positive spins (`Spin.Configuration`), `Spin.countLaw` is the
count pushforward, `Spin.Exchangeable` is permutation invariance.  Everything is proved for an
arbitrary law (arbitrary `ν : Configuration → ℝ`), so laws and probability vectors with zero
coordinates are covered.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim.Spin

/-! ### The converse map -/

/-- The converse map: the configuration with `j` positive spins receives `p_j / C(12,j)`. -/
def liftCount (p : Count → ℝ) (σ : Configuration) : ℝ :=
  p (plusCount σ) / ((12 : ℕ).choose σ.card : ℝ)

theorem liftCount_of_mem {p : Count → ℝ} {j : Count} {σ : Configuration}
    (hσ : σ ∈ countClass j) :
    liftCount p σ = p j / ((12 : ℕ).choose j.val : ℝ) := by
  have hh := (countClass_mem j σ).mp hσ
  unfold liftCount
  rw [hh, show σ.card = j.val from congrArg Fin.val hh]

theorem sum_countClass_liftCount (p : Count → ℝ) (j : Count) :
    (∑ σ ∈ countClass j, liftCount p σ) = p j := by
  rw [Finset.sum_congr rfl (fun σ hσ => liftCount_of_mem hσ)]
  simp only [Finset.sum_const, nsmul_eq_mul, countClass_card]
  field_simp [(countClass_pos j).ne']

/-- The count law of the lifted measure is the original probability vector. -/
theorem countLaw_liftCount (p : Count → ℝ) : countLaw (liftCount p) = p :=
  funext (sum_countClass_liftCount p)

theorem liftCount_nonneg {p : Count → ℝ} (hp : ∀ j, 0 ≤ p j) (σ : Configuration) :
    0 ≤ liftCount p σ :=
  div_nonneg (hp _) (Nat.cast_nonneg _)

theorem liftCount_mass {p : Count → ℝ} (hp : (∑ j, p j) = 1) :
    (∑ σ, liftCount p σ) = 1 := by
  rw [← countLaw_mass, countLaw_liftCount, hp]

theorem liftCount_exchangeable (p : Count → ℝ) : Exchangeable (liftCount p) := by
  intro π σ
  simp [liftCount, plusCount, Finset.card_map]

/-- The probability of the all-minus configuration (empty positive set) is `p_0`. -/
theorem liftCount_empty (p : Count → ℝ) : liftCount p ∅ = p 0 := by
  simp [liftCount, plusCount]

theorem countLaw_zero (ν : Configuration → ℝ) : countLaw ν 0 = ν ∅ := by
  simp [countLaw, countClass]

/-! ### Moments of arbitrary spin products on count classes -/

/-- The joint moment over a count class depends only on the cardinality of `S`
(a refinement of `Spin.count_joint_moment`, which treats initial segments). -/
theorem count_joint_moment_card (S : Finset (Fin 12)) (s : Order) (hS : S.card = s.val + 1)
    (j : Count) :
    (∑ σ ∈ countClass j, jointSpin S σ) = ((12 : ℕ).choose j.val : ℝ) * moment s j := by
  have h := congrArg (fun a : ℚ => (a : ℝ)) (show
      (∑ σ ∈ countClass j, jointSpinQ S σ) = ((12 : ℕ).choose j.val : ℚ) * momentQ s j by
    rw [countClass, sum_countClass_eq_coeff, prod_split, hS,
      show 12 - (s.val + 1) = 11 - s.val by omega, coeff_mixed, mixedCoeff_eq_moment])
  simpa only [Rat.cast_sum, jointSpin_cast, Rat.cast_mul, Rat.cast_natCast, moment] using h

theorem exchangeable_joint_moment_card {ν : Configuration → ℝ} (hν : Exchangeable ν)
    (S : Finset (Fin 12)) (s : Order) (hS : S.card = s.val + 1) :
    (∑ σ : Configuration, ν σ * jointSpin S σ) = ∑ j : Count, moment s j * countLaw ν j := by
  rw [sum_count_classes]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ σ ∈ countClass j, (countLaw ν j / ((12 : ℕ).choose j.val : ℝ)) * jointSpin S σ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have hh := (countClass_mem j σ).mp hσ
      have he := law_eq_countLaw_div hν σ
      rw [he, hh, show σ.card = j.val from congrArg Fin.val hh]
    _ = _ := by
      rw [← Finset.mul_sum, count_joint_moment_card S s hS]
      field_simp [(countClass_pos j).ne']

/-- Common spin mean: for an exchangeable law, every single spin has mean `Σ_j x_j p_j`
(`eq:section5-spin-count-identities` with `s = 1`, for every coordinate). -/
theorem exchangeable_single_spin_mean {ν : Configuration → ℝ} (hν : Exchangeable ν)
    (i : Fin 12) :
    (∑ σ : Configuration, ν σ * jointSpin {i} σ) = mean (countLaw ν) := by
  rw [exchangeable_joint_moment_card hν {i} 0 (by simp)]
  simp_rw [moment_zero_eq_meanCoordinate]
  rfl

/-! ### Identification of the entropy and the weighted moments -/

/-- `Hr(ν | μ_spin) = Σ_j p_j log(p_j/b_j)` (`eq:section5-spin-count-identities`), including laws
with zero coordinates (`0 log 0 = 0`). -/
theorem relativeEntropy_eq_count {ν : Configuration → ℝ} (hν : Exchangeable ν) :
    (∑ σ : Configuration, ν σ * Real.log (ν σ / (1 / 4096))) =
      relativeEntropy (countLaw ν) reference :=
  exchangeable_entropy hν

/-- The initial segment of the first `r` coordinates, `1 ≤ r ≤ 12`. -/
def firstR (r : ℕ) : Finset (Fin 12) := Finset.univ.filter (fun i : Fin 12 => i.val < r)

theorem firstR_succ (s : Order) : firstR (s.val + 1) = firstCoordinates s := rfl

/-- The printed weighted sum of squared joint moments
`Σ_{r=1}^{12} C(12,r) 2^{r-1}/r^6 (E_ν[σ_1⋯σ_r])^2` equals the quadratic form `p^T W p`. -/
theorem printed_energy_eq_quadratic {ν : Configuration → ℝ} (hν : Exchangeable ν) :
    (∑ r ∈ Finset.Icc 1 12, ((12 : ℕ).choose r : ℝ) * 2 ^ (r - 1) / (r : ℝ) ^ 6 *
        (∑ σ : Configuration, ν σ * jointSpin (firstR r) σ) ^ 2) =
      quadratic (countLaw ν) := by
  rw [← exchangeable_energy hν]
  have h1 : (∑ s : Order, weight s * (∑ σ : Configuration, ν σ * jointSpin (firstCoordinates s) σ) ^ 2) =
      ∑ k ∈ Finset.range 12, ((12 : ℕ).choose (k + 1) : ℝ) * 2 ^ k / ((k + 1 : ℕ) : ℝ) ^ 6 *
        (∑ σ : Configuration, ν σ * jointSpin (firstR (k + 1)) σ) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ((12 : ℕ).choose (k + 1) : ℝ) * 2 ^ k / ((k + 1 : ℕ) : ℝ) ^ 6 *
        (∑ σ : Configuration, ν σ * jointSpin (firstR (k + 1)) σ) ^ 2) 12]
    apply Finset.sum_congr rfl
    intro s _
    simp only [weight, weightQ, firstR_succ, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one]
    push_cast
    ring
  rw [h1, show Finset.Icc 1 12 = Finset.Ico 1 13 from rfl, Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr (by norm_num)
  intro k _
  rw [add_comm 1 k]
  simp

/-! ### The feasible set and the converse -/

/-- Forward direction: the count law of an exchangeable-or-not probability law with the
all-minus cap lies in the feasible set `𝒫`. -/
theorem feasible_countLaw {ν : Configuration → ℝ} (hnn : ∀ σ, 0 ≤ ν σ) (hmass : (∑ σ, ν σ) = 1)
    (hcap : ν ∅ ≤ 1 / 4096) : Feasible (countLaw ν) := by
  refine ⟨countLaw_nonneg hnn, ?_, ?_⟩
  · rw [countLaw_mass, hmass]
  · rw [countLaw_zero]; exact hcap

/-- Mean of an exchangeable probability law: the common spin mean equals the mean of its
count law, for every coordinate. -/
theorem mean_countLaw_eq {ν : Configuration → ℝ} (hν : Exchangeable ν) (i : Fin 12) :
    mean (countLaw ν) = ∑ σ : Configuration, ν σ * jointSpin {i} σ :=
  (exchangeable_single_spin_mean hν i).symm

/-- **Converse map** (sentence after `eq:section5-spin-count-probabilities`): every
`p ∈ 𝒫_t` (including vectors with zero coordinates) is the count vector of the exchangeable
probability measure `liftCount p` with common spin mean `t`, all-minus probability `p_0 ≤ 2^{-12}`,
and relative entropy `Σ_j p_j log(p_j/b_j)`. -/
theorem liftCount_converse {t : ℝ} {p : Count → ℝ} (hp : FeasibleAt t p) :
    Exchangeable (liftCount p) ∧ (∀ σ, 0 ≤ liftCount p σ) ∧ (∑ σ, liftCount p σ) = 1 ∧
      (∀ i : Fin 12, (∑ σ : Configuration, liftCount p σ * jointSpin {i} σ) = t) ∧
      liftCount p ∅ ≤ 1 / 4096 ∧ countLaw (liftCount p) = p ∧
      (∑ σ : Configuration, liftCount p σ * Real.log (liftCount p σ / (1 / 4096))) =
        relativeEntropy p reference := by
  obtain ⟨⟨hnn, hmass, hcap⟩, hmean⟩ := hp
  have hex := liftCount_exchangeable p
  refine ⟨hex, liftCount_nonneg hnn, liftCount_mass hmass, ?_, ?_, countLaw_liftCount p, ?_⟩
  · intro i
    rw [← mean_countLaw_eq hex i, countLaw_liftCount, hmean]
  · rw [liftCount_empty]; exact hcap
  · rw [relativeEntropy_eq_count hex, countLaw_liftCount]

/-- The spin-product moments of the lifted measure are the linear functionals `Σ_j A_{s,j} p_j`. -/
theorem liftCount_moment (p : Count → ℝ) (s : Order) :
    (∑ σ : Configuration, liftCount p σ * jointSpin (firstCoordinates s) σ) =
      ∑ j : Count, moment s j * p j := by
  rw [exchangeable_joint_moment (liftCount_exchangeable p) s, countLaw_liftCount]

/-- `Psi` of the finite-state package and of Lemma 5.16 agree. -/
theorem psi_eq_psiV2 (t : ℝ) : BecknerOnofri.V2.Circle.psi t = BecknerOnofri.V2.FiniteState.psiV2 t :=
  rfl

/-- **Proposition 5.12(ii), measure form, from its count form.**  The count form
`hcount` (the inequality `F(p) + 12ψ(t) ≥ t^4/250` for every `p ∈ 𝒫_t`, `t ∈ [0,1]`) is the content of
the finite-state packages G11-G14 and is an explicit hypothesis here.  This theorem proves that it
implies the printed statement for every exchangeable probability measure `ν` on `{-1,1}^{12}`
with common spin mean `t` and all-minus probability at most `2^{-12}`
(`eq:section5-global-spin-final`). -/
theorem spin_final_of_count_form
    (hcount : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ p : Count → ℝ, FeasibleAt t p →
      t ^ 4 / 250 ≤ functional p + 12 * BecknerOnofri.V2.Circle.psi t)
    {ν : Configuration → ℝ} (hν : Exchangeable ν) (hnn : ∀ σ, 0 ≤ ν σ)
    (hmass : (∑ σ, ν σ) = 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i : Fin 12, (∑ σ : Configuration, ν σ * jointSpin {i} σ) = t)
    (hcap : ν ∅ ≤ 1 / 4096) :
    t ^ 4 / 250 ≤
      2 * (∑ σ : Configuration, ν σ * Real.log (ν σ / (1 / 4096))) -
        (∑ r ∈ Finset.Icc 1 12, ((12 : ℕ).choose r : ℝ) * 2 ^ (r - 1) / (r : ℝ) ^ 6 *
          (∑ σ : Configuration, ν σ * jointSpin (firstR r) σ) ^ 2) +
        12 * BecknerOnofri.V2.Circle.psi t := by
  have hfeas : FeasibleAt t (countLaw ν) :=
    ⟨feasible_countLaw hnn hmass hcap, by rw [mean_countLaw_eq hν 0, hmean 0]⟩
  have h := hcount t ht (countLaw ν) hfeas
  rw [relativeEntropy_eq_count hν, printed_energy_eq_quadratic hν]
  unfold functional at h
  linarith

end BecknerOnofri.V2.Channel
