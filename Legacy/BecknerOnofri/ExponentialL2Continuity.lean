import Legacy.BecknerOnofri.ExponentialPartitionContinuity

/-! A quantitative L2 bound for exponentials from L2 convergence of the
potentials and their actual fourth exponential moments. -/
noncomputable section
namespace Legacy.BecknerOnofri.ExponentialL2Continuity
open MeasureTheory ExponentialPartitionContinuity

theorem exp_difference_sq_le (a b : ℝ) :
    (Real.exp a-Real.exp b)^2 ≤
      2 * |a-b| * (Real.exp (2*a)+Real.exp (2*b)) := by
  have h := abs_exp_sub_le a b
  have he : |Real.exp a-Real.exp b| ≤ Real.exp a+Real.exp b := by
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_pos (Real.exp_pos _)] using
      abs_sub_le (Real.exp a) 0 (Real.exp b)
  have hn := mul_le_mul h he (abs_nonneg _)
    (by positivity : 0 ≤ |a-b| * (Real.exp a+Real.exp b))
  have hp : (Real.exp a+Real.exp b)^2 ≤ 2*(Real.exp a^2+Real.exp b^2) := by
    nlinarith only [sq_nonneg (Real.exp a-Real.exp b)]
  have ht := mul_le_mul_of_nonneg_left hp (abs_nonneg (a-b))
  have hsa : Real.exp (2*a) = Real.exp a^2 := by simpa using Real.exp_nat_mul a 2
  have hsb : Real.exp (2*b) = Real.exp b^2 := by simpa using Real.exp_nat_mul b 2
  rw [hsa, hsb]
  nlinarith only [hn, ht, sq_abs (Real.exp a-Real.exp b)]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exp_double_memLp_two (u : Lp ℂ 2 μ)
    (hu : Integrable (fun x => Real.exp (4*(u x).re)) μ) :
    MemLp (fun x => Real.exp (2*(u x).re)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (Real.continuous_exp.comp_aestronglyMeasurable
    ((Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).const_mul 2))).mpr
  have he : (fun x => Real.exp (2*(u x).re)^2) = (fun x => Real.exp (4*(u x).re)) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rwa [he]

theorem integral_norm_sub_mul_exp_double_le (u v w : Lp ℂ 2 μ)
    (hw : Integrable (fun x => Real.exp (4*(w x).re)) μ) :
    (∫ x, ‖u x-v x‖*Real.exp (2*(w x).re) ∂μ) ≤
      ‖u-v‖*Real.sqrt (∫ x, Real.exp (4*(w x).re) ∂μ) := by
  have hn : MemLp (fun x => ‖u x-v x‖) 2 μ := by
    simpa only [Pi.sub_apply] using ((Lp.memLp u).sub (Lp.memLp v)).norm
  have h := integral_mul_le_sqrt hn (exp_double_memLp_two w hw)
  rw [integral_norm_sub_sq, Real.sqrt_sq_eq_abs, abs_norm] at h
  have he : (fun x => Real.exp (2*(w x).re)^2) = (fun x => Real.exp (4*(w x).re)) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rwa [he] at h

theorem squared_difference_bound (u v : Lp ℂ 2 μ)
    (hu2 : Integrable (fun x => Real.exp (2*(u x).re)) μ)
    (hv2 : Integrable (fun x => Real.exp (2*(v x).re)) μ)
    (hu4 : Integrable (fun x => Real.exp (4*(u x).re)) μ)
    (hv4 : Integrable (fun x => Real.exp (4*(v x).re)) μ) :
    (∫ x, (Real.exp (u x).re-Real.exp (v x).re)^2 ∂μ) ≤
      2*‖u-v‖*(Real.sqrt (∫ x, Real.exp (4*(u x).re) ∂μ)+
        Real.sqrt (∫ x, Real.exp (4*(v x).re) ∂μ)) := by
  have hn : MemLp (fun x => ‖u x-v x‖) 2 μ := by
    simpa only [Pi.sub_apply] using ((Lp.memLp u).sub (Lp.memLp v)).norm
  have hnu : Integrable (fun x => ‖u x-v x‖*Real.exp (2*(u x).re)) μ :=
    hn.integrable_mul (exp_double_memLp_two u hu4)
  have hnv : Integrable (fun x => ‖u x-v x‖*Real.exp (2*(v x).re)) μ :=
    hn.integrable_mul (exp_double_memLp_two v hv4)
  have hi : Integrable (fun x => 2*‖u x-v x‖*(Real.exp (2*(u x).re)+Real.exp (2*(v x).re))) μ := by
    convert! (hnu.add hnv).const_mul 2 using 1
    funext x
    change 2*‖u x-v x‖*(Real.exp (2*(u x).re)+Real.exp (2*(v x).re)) =
      2*(‖u x-v x‖*Real.exp (2*(u x).re)+‖u x-v x‖*Real.exp (2*(v x).re))
    ring
  calc
    _ ≤ ∫ x, 2*‖u x-v x‖*(Real.exp (2*(u x).re)+Real.exp (2*(v x).re)) ∂μ := by
      apply integral_mono_ae ((exp_memLp_two u hu2).sub (exp_memLp_two v hv2)).integrable_sq hi
      filter_upwards [] with x
      apply (exp_difference_sq_le _ _).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (u x-v x)
    _ = 2*((∫ x, ‖u x-v x‖*Real.exp (2*(u x).re) ∂μ)+
        (∫ x, ‖u x-v x‖*Real.exp (2*(v x).re) ∂μ)) := by
      rw [← integral_add hnu hnv, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ ≤ _ := by
      have h1 := integral_norm_sub_mul_exp_double_le u v u hu4
      have h2 := integral_norm_sub_mul_exp_double_le u v v hv4
      nlinarith

theorem norm_sub_toLp_sq {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f-hg.toLp g‖^2 = ∫ x, (f x-g x)^2 ∂μ := by
  have h := real_inner_self_eq_norm_sq (hf.toLp f-hg.toLp g)
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy hz
  rw [hx]
  change ((hf.toLp f) x-(hg.toLp g) x)*((hf.toLp f) x-(hg.toLp g) x) = (f x-g x)^2
  rw [hy, hz, sq]

#print axioms squared_difference_bound
end Legacy.BecknerOnofri.ExponentialL2Continuity
