module

public import BecknerOnofri.SelectedConditionalProfile

@[expose] public section

/-! The conditional gamma estimates integrated against the actual joint density,
combined with discrete spin entropy and closed by nonnegative finite sums.
The selected application uses actual Fourier coefficients and their proven
reality and permutation symmetry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem conditional_profile_stats {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (x : Torus d)
    (F : ℝ → ℝ) (hcF : ContinuousOn F (Icc (-1 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (-1 : ℝ) 1) F) (hinc : MonotoneOn F (Icc (-1 : ℝ) 1))
    (hprofile : ∀ z, conditionalDensity f i x z = Real.exp (F (fourier 1 z).re)) :
    0 ≤ conditionalCosineMoment f i 1 x ∧ conditionalCosineMoment f i 1 x < 1 ∧
    Summable (fun n : ℕ => (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) := by
  let p : Torus 1 → ℝ := fun z => conditionalDensity f i x (z 0)
  have hp : Continuous p := by
    have hcos : Continuous (fun z : Torus 1 => (fourier 1 (z 0)).re) := by fun_prop
    have hcirc : Continuous (fun z : Torus 1 => F (fourier 1 (z 0)).re) :=
      hcF.comp_continuous hcos (fun z => ⟨(cosineVector_mem z).1 0, (cosineVector_mem z).2 0⟩)
    have heq : p = fun z => Real.exp (F (fourier 1 (z 0)).re) := funext (fun z => hprofile (z 0))
    rw [heq]
    exact Real.continuous_exp.comp hcirc
  have hm : (∫ z, p z ∂torusMeasure 1) = 1 := by
    rw [CirclePoisson.integral_torus_circle]
    exact conditional_density_mass hf i x
  have hmom (n : ℕ) : CirclePoisson.moment p n = conditionalCosineMoment f i n x :=
    CirclePoisson.moment_eq_cosine_integral p hp n
  have hmass : (∫ z : UnitAddCircle, Real.exp (F (fourier 1 z).re) ∂AddCircle.haarAddCircle) = 1 := by
    simpa only [← hprofile] using conditional_density_mass hf i x
  have hmean : (∫ z : UnitAddCircle, Real.exp (F (fourier 1 z).re) * (fourier 1 z).re ∂AddCircle.haarAddCircle) =
      conditionalCosineMoment f i 1 x := by simp only [← hprofile, conditionalCosineMoment, Nat.cast_one]
  have ht := CircleScalar.circle_comparison_on F _ hcF hF hinc hmass hmean
  refine ⟨ht.1, ht.2.1, ?_⟩
  have heven : ∀ z, p (-z) = p z := by
    intro z
    dsimp only [p]
    rw [hprofile, hprofile]
    simp only [Pi.neg_apply, fourier_apply, zsmul_neg, AddCircle.toCircle_neg]
    simp
  have hs := (CircleOuter.density_parseval p hp heven hm).1
  have hs' : Summable (fun n : ℕ => (conditionalCosineMoment f i (n+1) x)^2) := by
    simpa only [← hmom, CirclePoisson.moment, Nat.cast_add, Nat.cast_one] using hs
  have hs3 : Summable (fun n : ℕ => (conditionalCosineMoment f i (n+3) x)^2) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff 2).mpr hs'
  apply hs3.of_nonneg_of_le (fun n => by positivity)
  intro n
  exact div_le_self (sq_nonneg _) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

end BecknerOnofri.HighDim.ConditionalEntropy

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.BecknerOnofri.TorusSobolev ConditionalEntropy

theorem selected_conditional_mean_range {u : TorusL2 12} (hu : Selected u)
    (i : Fin 12) (x : HighDim.Torus 12) :
    conditionalCosineMoment (spinDensity hu).value i 1 x ∈ Ico (0 : ℝ) 1 := by
  obtain ⟨hc,hcv,hm⟩ := selected_log_profile_shape hu
  obtain ⟨F,hcF,hF,hmF,hrep⟩ := conditional_log_profile (logarithmicCosineProfile u)
    hc hcv hm _ (selected_log_profile_representation hu) i x
  have h := conditional_profile_stats (spinDensity_positiveBounded hu) i x F hcF hF hmF hrep
  exact ⟨h.1,h.2.1⟩

theorem selected_conditional_gamma_finite {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hψ : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t)
    (i : Fin 12) (x : HighDim.Torus 12) (s : Finset ℕ) :
    2 * Spin.binaryCost (conditionalCosineMoment (spinDensity hu).value i 1 x) +
      ψ (conditionalCosineMoment (spinDensity hu).value i 1 x) +
      (21/1000) * (conditionalCosineMoment (spinDensity hu).value i 2 x)^2 +
      (27/40) * (∑ n ∈ s, (conditionalCosineMoment (spinDensity hu).value i (n+3) x)^2 / (n+3 : ℝ)) ≤
        conditionalEntropy (spinDensity hu).value i x := by
  obtain ⟨hc,hcv,hm⟩ := selected_log_profile_shape hu
  obtain ⟨F,hcF,hF,hmF,hrep⟩ := conditional_log_profile (logarithmicCosineProfile u)
    hc hcv hm _ (selected_log_profile_representation hu) i x
  obtain ⟨h0,h1,hs⟩ := conditional_profile_stats (spinDensity_positiveBounded hu) i x F hcF hF hmF hrep
  have hminor := hψ _ ⟨h0,h1⟩
  have hsum := Summable.sum_le_tsum s (fun n _ => by positivity) hs
  have h := selected_conditional_gamma hu i x
  linarith

#print axioms selected_conditional_gamma_finite
end BecknerOnofri.HighDim.SelectedNumericalModel

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

theorem bounded_comp_Icc {d : ℕ} {u : Torus d → ℝ} (hu : BoundedMeasurable u)
    {a b : ℝ} (hr : ∀ x, u x ∈ Icc a b) (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b)) :
    BoundedMeasurable (fun x => ψ (u x)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  exact ⟨hc.restrict.measurable.comp (hu.1.subtype_mk (h := hr)), C,
    fun x => hC (mem_image_of_mem (fun y => ‖ψ y‖) (hr x))⟩

theorem integrate_conditional_budget {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (hm : (∫ x, f x ∂torusMeasure 12) = 1) (ψ : ℝ → ℝ)
    (hc : ContinuousOn ψ (Icc (0 : ℝ) 1)) (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (i : Fin 12) (s : Finset ℕ)
    (hr : ∀ x, conditionalCosineMoment f i 1 x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ x,
      2 * Spin.binaryCost (conditionalCosineMoment f i 1 x) +
      ψ (conditionalCosineMoment f i 1 x) + (21/1000) * (conditionalCosineMoment f i 2 x)^2 +
      (27/40) * (∑ n ∈ s, (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) ≤ conditionalEntropy f i x) :
    2 * (∫ x, f x * Spin.binaryCost (conditionalCosineMoment f i 1 x) ∂torusMeasure 12) +
      ψ (∫ x, f x * (fourier 1 (x i)).re ∂torusMeasure 12) +
      (21/1000) * (∫ x, f x * (fourier 2 (x i)).re ∂torusMeasure 12)^2 +
      (27/40) * (∑ n ∈ s, (∫ x, f x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
        ∫ x, f x * conditionalEntropy f i x ∂torusMeasure 12 := by
  let R := fun n => conditionalCosineMoment f i n
  let B := fun x => f x * Spin.binaryCost (R 1 x)
  let P := fun x => f x * ψ (R 1 x)
  let Q := fun n x => f x * (R n x)^2
  have hB : Integrable B (torusMeasure 12) :=
    (hf.bounded.mul (Spin.conditional_binaryCost_bounded hf i)).integrable
  have hP : Integrable P (torusMeasure 12) :=
    (hf.bounded.mul (bounded_comp_Icc (conditional_moment_bounded hf i 1) hr ψ hc)).integrable
  have hQ (n : ℕ) : Integrable (Q n) (torusMeasure 12) := by
    simpa only [Q, R, pow_two] using
      (hf.bounded.mul ((conditional_moment_bounded hf i n).mul (conditional_moment_bounded hf i n))).integrable
  have hsum : Integrable (fun x => ∑ n ∈ s, Q (n+3) x / (n+3 : ℝ)) (torusMeasure 12) :=
    integrable_finsetSum s (fun n _ => (hQ (n+3)).div_const _)
  have hent := (hf.bounded.mul (conditional_entropy_bounded hf i)).integrable
  have hmult (x : Torus 12) :
      2 * B x + P x + (21/1000) * Q 2 x +
      (27/40) * (∑ n ∈ s, Q (n+3) x / (n+3 : ℝ)) ≤ f x * conditionalEntropy f i x := by
    have h := mul_le_mul_of_nonneg_left (hb x) (hf.pos x).le
    dsimp only [B, P, Q, R]
    have ht : (∑ n ∈ s, f x * (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) =
        f x * (∑ n ∈ s, (conditionalCosineMoment f i (n+3) x)^2 / (n+3 : ℝ)) := by
      simp only [Finset.mul_sum, mul_div_assoc]
    rw [ht]
    nlinarith
  have h := integral_mono (((hB.const_mul 2).add hP).add ((hQ 2).const_mul (21/1000)) |>.add
    (hsum.const_mul (27/40))) hent hmult
  simp only [Pi.add_apply] at h
  rw [integral_add (f := fun x => 2 * B x + P x + (21/1000) * Q 2 x)
    (g := fun x => (27/40) * ∑ n ∈ s, Q (n+3) x / (n+3 : ℝ)) (((hB.const_mul 2).add hP).add ((hQ 2).const_mul (21/1000)))
    (hsum.const_mul (27/40)), integral_add (f := fun x => 2 * B x + P x) (g := fun x => (21/1000) * Q 2 x)
      ((hB.const_mul 2).add hP) ((hQ 2).const_mul (21/1000)),
    integral_add (f := fun x => 2 * B x) (g := P) (hB.const_mul 2) hP] at h
  simp only [integral_const_mul] at h
  rw [integral_finsetSum s (fun n _ => (hQ (n+3)).div_const _)] at h
  simp only [integral_div] at h
  have hψ := conditional_moment_jensen hf hm i 1 hr ψ hc hcv
  have h2 := conditional_moment_full_square hf hm i 2
  have ht : (∑ n ∈ s, (∫ x, f x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      ∑ n ∈ s, (∫ x, Q (n+3) x ∂torusMeasure 12) / (n+3 : ℝ) := by
    apply Finset.sum_le_sum
    intro n _
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using conditional_moment_full_square hf hm i (n+3)
  dsimp only [B, P, Q, R] at h
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hψ h2
  dsimp only [Q, R] at ht
  linarith

#print axioms integrate_conditional_budget
end BecknerOnofri.HighDim.ConditionalEntropy

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.BecknerOnofri.TorusSobolev ConditionalEntropy

theorem selected_channel_entropy_finite {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) (s : Finset ℕ) :
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
      (∑ i : Fin 12, ψ (∫ x, (spinDensity hu).value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (27/40) * (∑ i : Fin 12, ∑ n ∈ s,
        (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      entropy (spinDensity hu) := by
  have hi (i : Fin 12) := integrate_conditional_budget (spinDensity_positiveBounded hu)
    (spinDensity hu).mass ψ hc hcv i s
    (fun x => ⟨(selected_conditional_mean_range hu i x).1,
      (selected_conditional_mean_range hu i x).2.le⟩)
    (fun x => selected_conditional_gamma_finite hu ψ hminor i x s)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [← entropy_chain_rule_full (spinDensity_positiveBounded hu) (spinDensity hu).mass] at h
  have hspin := selected_spin_entropy hu
  unfold entropy
  linarith

#print axioms selected_channel_entropy_finite
end BecknerOnofri.HighDim.SelectedNumericalModel

namespace BecknerOnofri.HighDim.ConditionalEntropy

theorem nonnegative_budget_limit (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (A B c : ℝ) (hc : 0 < c) (hb : ∀ s : Finset ℕ, A + c * ∑ n ∈ s, g n ≤ B) :
    Summable g ∧ A + c * ∑' n, g n ≤ B := by
  have hsum (s : Finset ℕ) : (∑ n ∈ s, g n) ≤ (B-A)/c := by
    apply (le_div_iff₀ hc).mpr
    have h := hb s
    nlinarith
  refine ⟨summable_of_sum_le hg hsum, ?_⟩
  have h := (le_div_iff₀ hc).mp (Real.tsum_le_of_sum_le hg hsum)
  nlinarith

end BecknerOnofri.HighDim.ConditionalEntropy

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.BecknerOnofri.TorusSobolev ConditionalEntropy

theorem selected_channel_entropy {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
      (∑ i : Fin 12, ψ (∫ x, (spinDensity hu).value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
      (21/1000) * (∑ i : Fin 12, (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2) +
      (27/40) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)) ≤
      entropy (spinDensity hu) := by
  let a := fun (i : Fin 12) (n : ℕ) =>
    (∫ x, (spinDensity hu).value x * (fourier (n+3 : ℤ) (x i)).re ∂torusMeasure 12)^2 / (n+3 : ℝ)
  let A := 2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
    (∑ i : Fin 12, ψ (∫ x, (spinDensity hu).value x * (fourier 1 (x i)).re ∂torusMeasure 12)) +
    (21/1000) * (∑ i : Fin 12, (∫ x, (spinDensity hu).value x * (fourier 2 (x i)).re ∂torusMeasure 12)^2)
  have ha (i : Fin 12) (n : ℕ) : 0 ≤ a i n := by dsimp [a]; positivity
  have hf (s : Finset ℕ) : A + (27/40) * (∑ n ∈ s, ∑ i : Fin 12, a i n) ≤ entropy (spinDensity hu) := by
    rw [Finset.sum_comm]
    exact selected_channel_entropy_finite hu ψ hc hcv hminor s
  obtain ⟨hs,hb⟩ := nonnegative_budget_limit (fun n => ∑ i : Fin 12, a i n)
    (fun n => Finset.sum_nonneg (fun i _ => ha i n)) A (entropy (spinDensity hu)) (27/40) (by norm_num) hf
  have hi (i : Fin 12) : Summable (a i) :=
    hs.of_nonneg_of_le (ha i) (fun n => Finset.single_le_sum (fun j _ => ha j n) (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb

#print axioms selected_channel_entropy
end BecknerOnofri.HighDim.SelectedNumericalModel

namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SmoothFourier ContinuousGibbs ContinuousSymmetry

theorem density_coefficient_real {u : TorusL2 12} (hu : Selected u) (k : HighDim.Frequency 12) :
    (HighDim.fourierCoeff (spinDensity hu).value k).im = 0 := by
  obtain ⟨w,N,hw,hm,_,he⟩ := spinDensity_mixture hu
  change (densityFourier (spinDensity hu).value k).im = 0
  rw [he, CosineMixtureTransfer.rho_fourier w N hw hm.summable]
  rfl

theorem density_axis_re {u : TorusL2 12} (hu : Selected u) (i : Fin 12) (n : ℤ) :
    (HighDim.fourierCoeff (spinDensity hu).value (Pi.single i n)).re =
      ∫ x, (spinDensity hu).value x * (fourier n (x i)).re ∂HighDim.torusMeasure 12 := by
  have hf := smoothGibbsValue_continuous u (fourier_norm_summable hu)
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-Pi.single i n) x *
      ((spinDensity hu).value x : ℂ)) (HighDim.torusMeasure 12) :=
    ((UnitAddTorus.mFourier _).continuous.mul (Complex.continuous_ofReal.comp hf)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold HighDim.fourierCoeff
  have hre := integral_re hi
  change (∫ x, (UnitAddTorus.mFourier (-Pi.single i n) x *
      ((spinDensity hu).value x : ℂ)).re ∂HighDim.torusMeasure 12) =
    (∫ x, UnitAddTorus.mFourier (-Pi.single i n) x *
      ((spinDensity hu).value x : ℂ) ∂HighDim.torusMeasure 12).re at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [] with x
  have hchar (k : ℤ) : UnitAddTorus.mFourier (Pi.single i k) x = fourier k (x i) := by
    classical
    change (∏ j, fourier ((Pi.single i k : HighDim.Frequency 12) j) (x j)) = _
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  rw [← Pi.single_neg, hchar, fourier_neg]
  simp [Complex.mul_re, mul_comm]

theorem density_axis_norm_sq {u : TorusL2 12} (hu : Selected u) (i : Fin 12) (n : ℤ) :
    ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i n)‖^2 =
      (∫ x, (spinDensity hu).value x * (fourier n (x i)).re ∂HighDim.torusMeasure 12)^2 := by
  have h := Complex.sq_norm_sub_sq_im (HighDim.fourierCoeff (spinDensity hu).value (Pi.single i n))
  simpa only [density_coefficient_real hu, zero_pow (by decide : 2 ≠ 0), sub_zero, density_axis_re hu] using h

theorem density_axis_mean {u : TorusL2 12} (hu : Selected u) (i : Fin 12) :
    (∫ x, (spinDensity hu).value x * (fourier 1 (x i)).re ∂HighDim.torusMeasure 12) =
      Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu))) := by
  have h := CosineCoefficientLattice.selected_permutation_densityFourier hu
    (Equiv.swap (0 : Fin 12) i) (axisFrequency (0 : Fin 12))
  rw [frequencyPermutation_axis, Equiv.swap_apply_left] at h
  have haxis (j : Fin 12) : axisFrequency j = Pi.single j (1 : ℤ) := by
    funext k
    simp [axisFrequency, Pi.single_apply]
  rw [haxis, haxis] at h
  rw [← smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu),
    ← smoothGibbsDensity_fourier rough hu.1 (fourier_norm_summable hu)] at h
  have hre := congrArg Complex.re h
  change (HighDim.fourierCoeff (spinDensity hu).value (Pi.single i 1)).re =
    (HighDim.fourierCoeff (spinDensity hu).value (Pi.single (0 : Fin 12) 1)).re at hre
  rw [density_axis_re hu, density_axis_re hu] at hre
  exact hre.trans (Spin.channel_count_mean (spinDensity hu) (selected_spin_exchangeable hu)).symm

theorem selected_channel_fourier_entropy {u : TorusL2 12} (hu : Selected u)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1))
    (hcv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hminor : ∀ t ∈ Ico (0 : ℝ) 1, ψ t ≤ CircleScalar.gamma t) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ))) ∧
    2 * Spin.relativeEntropy (Spin.countLaw (Spin.channelLaw (spinDensity hu))) Spin.reference +
      12 * ψ (Spin.mean (Spin.countLaw (Spin.channelLaw (spinDensity hu)))) +
      (21/1000) * (∑ i : Fin 12, ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (2 : ℤ))‖^2) +
      (27/40) * (∑ i : Fin 12, ∑' n : ℕ,
        ‖HighDim.fourierCoeff (spinDensity hu).value (Pi.single i (n+3 : ℤ))‖^2 / (n+3 : ℝ)) ≤
      HighDim.entropy (spinDensity hu) := by
  have h := selected_channel_entropy hu ψ hc hcv hminor
  simpa only [density_axis_norm_sq hu, density_axis_mean hu, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using h

#print axioms selected_channel_fourier_entropy
end BecknerOnofri.HighDim.SelectedNumericalModel
