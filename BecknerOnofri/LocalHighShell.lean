import BecknerOnofri.LocalFourierMajorant

/-! Removing the actual zero and first Fourier shells from the product majorant. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace BecknerOnofri.HighDim

def localRadiusSq {d : ℕ} (k : Frequency d) : ℝ := ∑ i, (k i : ℝ) ^ 2
abbrev HigherFrequency (d : ℕ) := {k : Frequency d // 1 < localRadiusSq k}

def signedAxis {d : ℕ} (j : Fin d) (b : Bool) : Frequency d :=
  fun i => if i = j then (if b then 1 else -1) else 0

def lowFrequency {d : ℕ} : Option (Fin d × Bool) → Frequency d
  | none => 0
  | some (j, b) => signedAxis j b

lemma signedAxis_ne_zero {d : ℕ} (j : Fin d) (b : Bool) : signedAxis j b ≠ 0 := by
  intro h
  have hh := congrFun h j
  cases b <;> simp [signedAxis] at hh

lemma signedAxis_injective {d : ℕ} : Function.Injective (fun p : Fin d × Bool => signedAxis p.1 p.2) := by
  rintro ⟨j, b⟩ ⟨l, c⟩ h
  have hj : j = l := by
    by_contra hj
    have hh := congrFun h j
    cases b <;> simp [signedAxis, hj] at hh
  subst l
  have hb : b = c := by
    have hh := congrFun h j
    cases b <;> cases c <;> simp_all [signedAxis]
  subst c
  rfl

lemma lowFrequency_injective {d : ℕ} : Function.Injective (lowFrequency (d := d)) := by
  intro p q h
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q => exact False.elim (signedAxis_ne_zero q.1 q.2 h.symm)
  | some p =>
    cases q with
    | none => exact False.elim (signedAxis_ne_zero p.1 p.2 h)
    | some q => exact congrArg some (signedAxis_injective h)

lemma signedAxis_radiusSq {d : ℕ} (j : Fin d) (b : Bool) : localRadiusSq (signedAxis j b) = 1 := by
  classical
  cases b <;> simp [localRadiusSq, signedAxis]

lemma lowFrequency_radiusSq_le {d : ℕ} (p : Option (Fin d × Bool)) :
    localRadiusSq (lowFrequency p) ≤ 1 := by
  cases p with
  | none => simp [lowFrequency, localRadiusSq]
  | some p => rw [lowFrequency, signedAxis_radiusSq]

lemma firstShellFourierMajorant_zero {d : ℕ} (t : Fin d → ℝ) :
    firstShellFourierMajorant t 0 = 1 := by
  simp [firstShellFourierMajorant, circleFourierMajorant, besselSeriesTerm]

lemma firstShellFourierMajorant_signedAxis {d : ℕ} (t : Fin d → ℝ) (j : Fin d) (b : Bool) :
    firstShellFourierMajorant t (signedAxis j b) = t j ^ 2 := by
  classical
  cases b <;> simp [firstShellFourierMajorant, circleFourierMajorant, besselSeriesTerm,
    signedAxis, apply_ite]

lemma firstShellFourierMajorant_lowSum {d : ℕ} (t : Fin d → ℝ) :
    (∑ p : Option (Fin d × Bool), firstShellFourierMajorant t (lowFrequency p)) =
      1 + 2 * ∑ i, t i ^ 2 := by
  rw [Fintype.sum_option]
  simp_rw [lowFrequency, firstShellFourierMajorant_zero, Fintype.sum_prod_type,
    firstShellFourierMajorant_signedAxis, Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  ring

lemma firstShellFourierMajorant_higher_bound {d : ℕ} (t : Fin d → ℝ) :
    (∑' k : HigherFrequency d, firstShellFourierMajorant t k.val) ≤
      Real.exp (2 * ∑ i, t i ^ 2) - 1 - 2 * ∑ i, t i ^ 2 := by
  let e : (Option (Fin d × Bool)) ⊕ HigherFrequency d → Frequency d :=
    Sum.elim lowFrequency Subtype.val
  have he : Function.Injective e := by
    intro p q h
    cases p with
    | inl p =>
      cases q with
      | inl q => exact congrArg Sum.inl (lowFrequency_injective h)
      | inr q =>
        have hh := lowFrequency_radiusSq_le p
        have hq := q.property
        change lowFrequency p = q.val at h
        rw [h] at hh
        linarith
    | inr p =>
      cases q with
      | inl q =>
        have hh := lowFrequency_radiusSq_le q
        have hp := p.property
        change p.val = lowFrequency q at h
        rw [← h] at hh
        linarith
      | inr q => exact congrArg Sum.inr (Subtype.ext h)
  have hs := firstShellFourierMajorant_summable t
  have hse : Summable (fun p : (Option (Fin d × Bool)) ⊕ HigherFrequency d =>
      firstShellFourierMajorant t (e p)) := hs.comp_injective he
  have hh := Summable.tsum_le_tsum_of_inj
    (f := fun p : (Option (Fin d × Bool)) ⊕ HigherFrequency d => firstShellFourierMajorant t (e p))
    (g := firstShellFourierMajorant t) e he
    (fun k _ => firstShellFourierMajorant_nonneg t k) (fun _ => le_rfl) hse hs
  rw [Summable.tsum_sum (hse.comp_injective Sum.inl_injective)
    (hse.comp_injective Sum.inr_injective)] at hh
  change (∑' p : Option (Fin d × Bool), firstShellFourierMajorant t (lowFrequency p)) +
    (∑' k : HigherFrequency d, firstShellFourierMajorant t k.val) ≤
    ∑' k : Frequency d, firstShellFourierMajorant t k at hh
  rw [tsum_fintype (fun p : Option (Fin d × Bool) =>
    firstShellFourierMajorant t (lowFrequency p)), firstShellFourierMajorant_lowSum] at hh
  have htotal := firstShellFourierMajorant_tsum_le t
  linarith

#print axioms firstShellFourierMajorant_higher_bound
end BecknerOnofri.HighDim
