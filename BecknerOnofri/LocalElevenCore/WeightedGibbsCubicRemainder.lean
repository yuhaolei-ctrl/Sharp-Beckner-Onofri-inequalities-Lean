import BecknerOnofri.LocalElevenCore.WienerAlgebraBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.LocalEleven.WeightedGibbsCubicRemainder
open ContinuousGibbs ContinuousFirstShell GraphRegularity GraphWienerBounds
open WeightedExponentialRemainder WeightedCubicExponentialTail WienerAlgebraBounds
open BecknerOnofri.OnsetWienerBounds

lemma radial_quadratic {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u) (hm : mean d u=0) :
    Radial m (quadraticTerm u) := by
  rw [quadraticTerm_of_mean_zero hm]
  exact radial_smul m _ _ (radial_center m _ (by simpa only [pow_two] using radial_mul m u u hu hu))

lemma wienerSize_quadratic_le {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hm : mean d u=0) : wienerSize m (quadraticTerm u)≤(wienerSize m u)^2 := by
  rw [quadraticTerm_of_mean_zero hm,wienerSize_smul]
  have hu2 : Radial m (u^2) := by simpa only [pow_two] using radial_mul m u u hu hu
  have hc := wienerSize_center_le m (u^2) hu2
  have hp := wienerSize_mul_le m u u hu hu
  norm_num
  rw [← pow_two] at hp
  nlinarith

lemma mean_tail_bound {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hM : wienerSize m u≤1) : |mean d (exponentialTail u)|≤(wienerSize m u)^2 := by
  let M := wienerSize m u
  have h0 : 0≤M := radialSize_nonneg _ _
  have hm := mean_le_radialSize m (exponentialTail u) (exponentialTail_radial m u hu)
  have ht := exponentialTail_radialSize_le m u hu
  have hb := Real.exp_bound (x := M) (by simpa only [abs_of_nonneg h0] using hM)
    (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ,abs_of_nonneg h0] at hb
  change radialSize m (fun k => coefficient k (exponentialTail u))≤Real.exp M-1-M at ht
  have hh := le_abs_self (Real.exp M-(1+M))
  change _≤M^2
  nlinarith [sq_nonneg M]

lemma remainder_identity {d : ℕ} (u : Space d) (hm : mean d u=0) :
    nonlinearRemainder u-quadraticTerm u = (partition u)⁻¹ •
      (center d (tailThree u)-mean d (exponentialTail u) • u-
        mean d (exponentialTail u) • quadraticTerm u) := by
  have ht : mean d (exponentialTail u)=partition u-1 := by
    simp only [exponentialTail,map_sub,hm,mean_one,sub_zero,partition]
  have hmean : mean d (exponential u)=partition u := rfl
  rw [ht,quadraticTerm_of_mean_zero hm]
  ext x
  simp only [nonlinearRemainder,normalized,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    ContinuousMap.one_apply,smul_eq_mul,center_apply,hm,sub_zero,tailThree,
    map_sub,map_smul,mean_one,hmean,smul_eq_mul]
  have hZ := (partition_pos u).ne'
  field_simp
  ring

/-- The actual normalized Gibbs Taylor remainder is cubic in every fixed
polynomial Wiener norm, on its actual mean-zero domain. -/
theorem cubic_bound {d : ℕ} (m : ℕ) (u : Space d) (hu : Radial m u)
    (hm : mean d u=0) (hM : wienerSize m u≤1) :
    wienerSize m (nonlinearRemainder u-quadraticTerm u)≤4*(wienerSize m u)^3 := by
  let A := mean d (exponentialTail u)
  let Q := quadraticTerm u
  let T := center d (tailThree u)
  have hQ : Radial m Q := radial_quadratic m u hu hm
  have hT : Radial m T := radial_center m _ (tailThree_radial m u hu)
  have hAu : Radial m (A • u) := radial_smul m _ u hu
  have hAQ : Radial m (A • Q) := radial_smul m _ Q hQ
  have h1 := wienerSize_sub_le m (T-A • u) (A • Q) (radial_sub m T _ hT hAu) hAQ
  have h2 := wienerSize_sub_le m T (A • u) hT hAu
  rw [wienerSize_smul,Real.norm_eq_abs] at h1 h2
  have h3 := wienerSize_center_le m (tailThree u) (tailThree_radial m u hu)
  have h4 := tailThree_radial_bound m u hu hM
  have h5 := wienerSize_quadratic_le m u hu hm
  have h6 := mean_tail_bound m u hu hM
  have h0 : 0≤wienerSize m u := radialSize_nonneg _ _
  have hQ0 : 0≤wienerSize m Q := radialSize_nonneg _ _
  have hA0 : 0≤|A| := abs_nonneg _
  change |A|≤(wienerSize m u)^2 at h6
  change wienerSize m Q≤(wienerSize m u)^2 at h5
  change wienerSize m T≤2*wienerSize m (tailThree u) at h3
  change wienerSize m (tailThree u)≤(wienerSize m u)^3 at h4
  have hsmall : wienerSize m (T-A • u-A • Q)≤4*(wienerSize m u)^3 := by
    have ha := mul_le_mul_of_nonneg_right h6 h0
    have hq := mul_le_mul h6 h5 hQ0 (sq_nonneg _)
    have hpow := mul_le_mul_of_nonneg_right hM (pow_nonneg h0 3)
    nlinarith
  rw [remainder_identity u hm,wienerSize_smul]
  have hZ : ‖(partition u)⁻¹‖≤1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (partition_pos u).le)]
    exact inv_le_one_of_one_le₀ (partition_ge_one u hm)
  exact (mul_le_of_le_one_left (radialSize_nonneg _ _) hZ).trans hsmall

#print axioms cubic_bound
end BecknerOnofri.HighDim.LocalEleven.WeightedGibbsCubicRemainder
