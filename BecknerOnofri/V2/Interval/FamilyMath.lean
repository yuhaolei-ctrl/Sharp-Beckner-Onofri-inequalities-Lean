module

public import BecknerOnofri.V2.Interval.FamilySpec2

@[expose] public section

/-!
# Mathematical identification of the program's intermediate quantities (phases 3 and 4)
-/

namespace BecknerOnofri.V2.Interval

open BecknerOnofri.V2.FiniteState BecknerOnofri.HighDim.Spin Finset

theorem featQ : ∀ s : Order, ∀ j : Count,
    ((featureNum (s.val + 1) j.val : ℤ) : ℚ) / ((featureDen (s.val + 1) : ℕ) : ℚ) = momentQ s j := by
  decide +kernel

theorem weightQ_prog : ∀ s : Order,
    ((weightNum (s.val + 1) : ℤ) : ℚ) / ((weightDen (s.val + 1) : ℕ) : ℚ) = weightQ s := by
  decide +kernel

noncomputable def momR (s0 j : ℕ) : ℝ :=
  ((featureNum (s0 + 1) j : ℤ) : ℝ) / ((featureDen (s0 + 1) : ℕ) : ℝ)

noncomputable def wR (s0 : ℕ) : ℝ :=
  ((weightNum (s0 + 1) : ℤ) : ℝ) / ((weightDen (s0 + 1) : ℕ) : ℝ)

theorem momR_eq (s : Order) (j : Count) : momR s.val j.val = moment s j := by
  unfold momR moment
  rw [← featQ s j]
  push_cast
  rfl

theorem wR_eq (s : Order) : wR s.val = weight s := by
  unfold wR weight
  rw [← weightQ_prog s]
  push_cast
  rfl

theorem sum_range13 (F : ℕ → ℝ) : ∑ j ∈ range 13, F j = ∑ j : Count, F j.val :=
  (Fin.sum_univ_eq_sum_range F 13).symm

theorem sum_range12 (F : ℕ → ℝ) : ∑ j ∈ range 12, F j = ∑ j : Order, F j.val :=
  (Fin.sum_univ_eq_sum_range F 12).symm

theorem psVal_fin (t : ℝ) (j : Count) : psVal t j.val = famLaw t j := by
  simp [psVal]

noncomputable def lsVal (t : ℝ) (j : ℕ) : ℝ :=
  Real.log (psVal t j * (((Nat.choose 12 j : ℕ) : ℝ) / 4096)⁻¹)
noncomputable def msVal (t : ℝ) (s0 : ℕ) : ℝ := ∑ j ∈ range 13, psVal t j * momR s0 j
noncomputable def MpVal (t : ℝ) (j : ℕ) : ℝ :=
  ∑ s0 ∈ range 12, msVal t s0 * (wR s0 * momR s0 j)
noncomputable def entVal (t : ℝ) : ℝ := ∑ j ∈ range 13, psVal t j * lsVal t j
noncomputable def en2Val (t : ℝ) : ℝ := ∑ s0 ∈ range 12, msVal t s0 ^ 2 * wR s0
noncomputable def gVal (t : ℝ) (j : ℕ) : ℝ := (lsVal t j + 1 + -MpVal t j) * 2
/-- The gradient of `p(t)` as a function on `ℕ`. -/
noncomputable def gF (t : ℝ) (j : ℕ) : ℝ :=
  if hj : j < 13 then gradient (famLaw t) ⟨j, hj⟩ else 0

theorem ms_eq (t : ℝ) (s : Order) : msVal t s.val = ∑ j : Count, famLaw t j * moment s j := by
  unfold msVal
  rw [sum_range13]
  exact Finset.sum_congr rfl fun j _ => by rw [psVal_fin, momR_eq]

theorem interaction_eq (i j : Count) :
    interaction i j = ∑ s : Order, weight s * moment s i * moment s j := by
  unfold interaction interactionQ weight moment
  push_cast
  rfl

theorem Mp_eq (t : ℝ) (j : Count) :
    MpVal t j.val = ∑ k : Count, interaction j k * famLaw t k := by
  unfold MpVal
  rw [sum_range12]
  simp_rw [ms_eq, wR_eq, momR_eq, interaction_eq, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => by ring

theorem en2_eq (t : ℝ) : en2Val t = quadratic (famLaw t) := by
  unfold en2Val quadratic
  rw [sum_range12]
  simp_rw [ms_eq, wR_eq, interaction_eq]
  calc ∑ s : Order, (∑ i : Count, famLaw t i * moment s i) ^ 2 * weight s
      = ∑ s : Order, ∑ i : Count, ∑ j : Count,
          famLaw t i * famLaw t j * (weight s * moment s i * moment s j) :=
        Finset.sum_congr rfl fun s _ => by
          rw [pow_two, Finset.sum_mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i : Count, ∑ s : Order, ∑ j : Count,
          famLaw t i * famLaw t j * (weight s * moment s i * moment s j) := Finset.sum_comm
    _ = ∑ i : Count, ∑ j : Count, ∑ s : Order,
          famLaw t i * famLaw t j * (weight s * moment s i * moment s j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ => by ring

theorem ent_eq (t : ℝ) : entVal t = relativeEntropy (famLaw t) reference := by
  unfold entVal relativeEntropy
  rw [sum_range13]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [psVal_fin]
  unfold lsVal
  rw [psVal_fin, reference_eq]
  simp only [div_eq_mul_inv]

theorem g_eq (t : ℝ) (j : Count) : gVal t j.val = gradient (famLaw t) j := by
  unfold gVal gradient
  rw [Mp_eq]
  have : lsVal t j.val = Real.log (famLaw t j / reference j) := by
    unfold lsVal
    rw [psVal_fin, reference_eq]
    simp only [div_eq_mul_inv]
  rw [this]
  ring

theorem gVal_gF (t : ℝ) {j : ℕ} (hj : j < 13) : gVal t j = gF t j := by
  have := g_eq t ⟨j, hj⟩
  simpa [gF, hj] using this

theorem f_eq (t : ℝ) : entVal t * 2 + -en2Val t = functional (famLaw t) := by
  rw [ent_eq, en2_eq]
  unfold functional
  ring

theorem meang_eq (t : ℝ) :
    ∑ j ∈ range 13, psVal t j * gF t j = regMean (famLaw t) (gradient (famLaw t)) := by
  unfold regMean
  rw [sum_range13]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [psVal_fin]
  simp [gF]

end BecknerOnofri.V2.Interval
