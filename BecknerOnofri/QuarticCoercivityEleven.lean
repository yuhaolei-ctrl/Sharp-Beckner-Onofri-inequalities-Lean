import BecknerOnofri.QuarticSignsEleven

noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.LocalQuartic

theorem reducedQuartic_uniform {d : ℕ} (hd : 11 ≤ d) (δ : ℝ) :
    reducedQuartic d δ (fun _ => δ / kappa d) = (d : ℝ) / (2 * kappa d) * δ ^ 2 := by
  have hk := (kappa_positive hd).ne'
  have he : 2 * quarticA d + ((d : ℝ) - 1) * quarticB d = -kappa d := by
    unfold kappa
    ring
  simp only [reducedQuartic, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  nlinarith [he]

theorem reducedQuartic_coercive {d : ℕ} (hd : 11 ≤ d) (δ : ℝ) (r : Fin d → ℝ) :
    reducedQuartic d δ r ≤ (d : ℝ) / (2 * kappa d) * δ ^ 2 -
      kappa d / 2 * ∑ i, (r i - δ / kappa d) ^ 2 := by
  have hk := (kappa_positive hd).ne'
  have hb := (quarticB_positive hd).le
  have he : 2 * quarticA d + ((d : ℝ) - 1) * quarticB d = -kappa d := by
    unfold kappa
    ring
  have hCS : (∑ i, r i) ^ 2 ≤ (d : ℝ) * ∑ i, r i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := r)
  have hss : (∑ i, (r i - δ / kappa d) ^ 2) =
      (∑ i, r i ^ 2) - 2 * (δ / kappa d) * (∑ i, r i) + (d : ℝ) * (δ / kappa d) ^ 2 := by
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hbound := mul_le_mul_of_nonneg_left hCS (show 0 ≤ quarticB d / 2 by positivity)
  rw [hss]
  unfold reducedQuartic
  have hδ : kappa d * (δ / kappa d) = δ := mul_div_cancel₀ δ hk
  have htarget : (d : ℝ) / (2 * kappa d) * δ ^ 2 =
      (d : ℝ) * kappa d / 2 * (δ / kappa d) ^ 2 := by field_simp
  rw [htarget]
  nlinarith [congrArg (fun z : ℝ => z * (∑ i, r i ^ 2)) he,
    congrArg (fun z : ℝ => z * (∑ i, r i)) hδ]

theorem reducedQuartic_eq_max_iff {d : ℕ} (hd : 11 ≤ d) (δ : ℝ) (r : Fin d → ℝ) :
    reducedQuartic d δ r = (d : ℝ) / (2 * kappa d) * δ ^ 2 ↔
      r = fun _ => δ / kappa d := by
  constructor
  · intro he
    have h := reducedQuartic_coercive hd δ r
    rw [he] at h
    have hk := kappa_positive hd
    have hs : 0 ≤ ∑ i, (r i - δ / kappa d) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hz : (∑ i, (r i - δ / kappa d) ^ 2) = 0 := by nlinarith
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (r i - δ / kappa d))).mp
      hz i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro rfl
    exact reducedQuartic_uniform hd δ

theorem full_branch_pressure_coefficient {d : ℕ} (hd : 11 ≤ d) :
    -1 / (4 * branchQuarticCoefficient d d) = (d : ℝ) / (2 * kappa d) := by
  have hd0 : 0 < d := by omega
  have hdne : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd0).ne'
  have hk := (kappa_positive hd).ne'
  rw [branchQuarticCoefficient_full hd0]
  field_simp
  <;> norm_num


#print axioms reducedQuartic_coercive
end BecknerOnofri.HighDim.LocalQuartic
