module

public import BecknerOnofri.DiagonalStationaryBranch
public import BecknerOnofri.DiagonalParameterMonotonicity
public import BecknerOnofri.UniformComplementBounds

@[expose] public section

/-! Controlled inverse amplitude for the actual supercritical diagonal branch. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics Set
open scoped Topology
namespace BecknerOnofri.HighDim.DiagonalScalarBranch
open ContinuousGibbs ContinuousFirstShell ReducedCubicExpansion

structure BranchInterval {d : ℕ} (hd : 12 ≤ d) where
  radius : ℝ
  positive : 0 < radius
  strict : StrictMonoOn (parameter hd) (Icc 0 radius)
  continuous : ContinuousOn (parameter hd) (Icc 0 radius)
  lower : ∀ t ∈ Icc 0 radius, kappa d/2*t^2 ≤ parameter hd t-1
  regular : ∀ t ∈ Icc 0 radius, SmoothOnTorus (branchPotential hd t) ∧
    (∀ s : ℝ, InSobolev s (branchPotential hd t)) ∧
    ReducedEquation.full d (parameter hd t) (branchPotential hd t) = 0

theorem localInterval_exists {d : ℕ} (hd : 12 ≤ d) : Nonempty (BranchInterval hd) := by
  obtain ⟨s,hs,hm,hc⟩ := parameter_strictMonoOn hd
  obtain ⟨r,hr,hB⟩ := Metric.eventually_nhds_iff.mp
    ((parameter_lower_bound hd).and ((branchPotential_regular hd).and (branchPotential_full_zero hd)))
  let R := min s (r/2)
  have hR : 0 < R := lt_min hs (by positivity)
  have hsub : Icc 0 R ⊆ Icc 0 s := fun _ h => ⟨h.1,h.2.trans (min_le_left _ _)⟩
  have hdist {t : ℝ} (ht : t ∈ Icc 0 R) : dist t 0 < r := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    have ht' : t ≤ r/2 := ht.2.trans (min_le_right _ _)
    linarith
  refine ⟨⟨R,hR,hm.mono hsub,hc.mono hsub,?_,?_⟩⟩
  · intro t ht
    exact (hB (hdist ht)).1
  · intro t ht
    exact ⟨(hB (hdist ht)).2.1.1,(hB (hdist ht)).2.1.2,(hB (hdist ht)).2.2⟩

def localInterval {d : ℕ} (hd : 12 ≤ d) : BranchInterval hd :=
  Classical.choice (localInterval_exists hd)

def amplitudeRadius {d : ℕ} (hd : 12 ≤ d) : ℝ := (localInterval hd).radius

theorem amplitudeRadius_pos {d : ℕ} (hd : 12 ≤ d) : 0 < amplitudeRadius hd :=
  (localInterval hd).positive

def upperParameter {d : ℕ} (hd : 12 ≤ d) : ℝ := parameter hd (amplitudeRadius hd)

theorem upperParameter_gt_one {d : ℕ} (hd : 12 ≤ d) : 1 < upperParameter hd := by
  change 1 < parameter hd (localInterval hd).radius
  convert (localInterval hd).strict
    ⟨le_rfl,(localInterval hd).positive.le⟩ ⟨(localInterval hd).positive.le,le_rfl⟩
    (localInterval hd).positive using 1 <;> first | rfl | simp

theorem amplitude_exists {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ : μ ∈ Icc 1 (upperParameter hd)) :
    ∃ t : ℝ, t ∈ Icc 0 (amplitudeRadius hd) ∧ parameter hd t = μ := by
  apply intermediate_value_Icc (localInterval hd).positive.le (localInterval hd).continuous
  simpa only [parameter_base,upperParameter,amplitudeRadius] using hμ

/-- Positive inverse amplitude; outside the fixed local parameter interval it is set to zero. -/
def amplitude {d : ℕ} (hd : 12 ≤ d) (μ : ℝ) : ℝ :=
  if h : μ ∈ Icc 1 (upperParameter hd) then (amplitude_exists hd h).choose else 0

theorem amplitude_spec {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ : μ ∈ Icc 1 (upperParameter hd)) :
    amplitude hd μ ∈ Icc 0 (amplitudeRadius hd) ∧ parameter hd (amplitude hd μ) = μ := by
  simp only [amplitude,dif_pos hμ]
  exact (amplitude_exists hd hμ).choose_spec

theorem amplitude_nonneg {d : ℕ} (hd : 12 ≤ d) (μ : ℝ) : 0 ≤ amplitude hd μ := by
  by_cases hμ : μ ∈ Icc 1 (upperParameter hd)
  · exact (amplitude_spec hd hμ).1.1
  · simp only [amplitude,dif_neg hμ,le_refl]

theorem amplitude_pos {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ : 1 < μ) (hupper : μ ≤ upperParameter hd) : 0 < amplitude hd μ := by
  have hs := amplitude_spec hd ⟨hμ.le,hupper⟩
  apply lt_of_le_of_ne hs.1.1
  intro hz
  rw [← hz,parameter_base] at hs
  linarith [hs.2]

theorem amplitude_unique {d : ℕ} (hd : 12 ≤ d) {μ t : ℝ}
    (hμ : μ ∈ Icc 1 (upperParameter hd)) (ht : t ∈ Icc 0 (amplitudeRadius hd))
    (he : parameter hd t = μ) : t = amplitude hd μ :=
  (localInterval hd).strict.injOn ht (amplitude_spec hd hμ).1 (he.trans (amplitude_spec hd hμ).2.symm)

theorem eventually_parameter_interval {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), μ ∈ Icc 1 (upperParameter hd) := by
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds (upperParameter_gt_one hd)).filter_mono nhdsWithin_le_nhds] with μ hμ hu
  exact ⟨le_of_lt hμ,le_of_lt hu⟩

theorem amplitude_eventually_inverse {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), parameter hd (amplitude hd μ) = μ :=
  (eventually_parameter_interval hd).mono (fun _ h => (amplitude_spec hd h).2)

theorem amplitude_tendsto {d : ℕ} (hd : 12 ≤ d) :
    Tendsto (amplitude hd) (𝓝[>] (1:ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hk : 0 < kappa d/2*ε^2 := by have := kappa_pos d hd; positivity
  have hμ : ∀ᶠ μ in 𝓝[>] (1:ℝ), μ-1 < kappa d/2*ε^2 := by
    have ht : Tendsto (fun μ : ℝ => μ-1) (𝓝[>] 1) (𝓝 0) := by
      have hi : Tendsto (fun μ : ℝ => μ) (𝓝 (1:ℝ)) (𝓝 1) := tendsto_id
      simpa only [sub_self] using (hi.sub_const (1:ℝ)).mono_left nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds hk)
  filter_upwards [eventually_parameter_interval hd,hμ] with μ hi hsmall
  have hs := amplitude_spec hd hi
  have hl := (localInterval hd).lower _ hs.1
  rw [hs.2] at hl
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hs.1.1]
  have hk0 : 0 < kappa d/2 := by have := kappa_pos d hd; positivity
  have hsq := (mul_lt_mul_iff_right₀ hk0).mp (hl.trans_lt hsmall)
  nlinarith

/-- Physical onset parameter, normalized as in the trusted statement. -/
def onset (μ : ℝ) : ℝ := 1-1/μ

theorem onset_pos {μ : ℝ} (hμ : 1 < μ) : 0 < onset μ := by
  unfold onset
  have hm : 0 < μ := by linarith
  exact sub_pos.mpr ((div_lt_one hm).mpr hμ)

theorem onset_identity {μ : ℝ} (hμ : μ ≠ 0) : μ*onset μ = μ-1 := by
  unfold onset
  field_simp

theorem onset_tendsto : Tendsto onset (𝓝[>] (1:ℝ)) (𝓝 0) := by
  have hc : ContinuousAt onset 1 := continuousAt_const.sub (continuousAt_const.div continuousAt_id (by norm_num))
  simpa [onset] using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem amplitude_square_bound {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => (amplitude hd μ)^2) =O[𝓝[>] (1:ℝ)] onset := by
  apply IsBigO.of_bound (4/kappa d)
  filter_upwards [eventually_parameter_interval hd,self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds] with μ hi hμ hu
  change 1 < μ at hμ
  have hs := amplitude_spec hd hi
  have hl := (localInterval hd).lower _ hs.1
  rw [hs.2] at hl
  have hk := kappa_pos d hd
  have ho := onset_pos hμ
  have hm : μ ≠ 0 := by linarith
  have he := onset_identity hm
  simp only [Real.norm_eq_abs,abs_sq,abs_of_pos ho]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hk).mpr
  have hineq : (amplitude hd μ)^2*kappa d ≤ 4*onset μ := by
    nlinarith [mul_lt_mul_of_pos_right hu ho]
  simpa [div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hineq

theorem amplitude_stationary {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ : 1 < μ) (hu : μ ≤ upperParameter hd) :
    branchPotential hd (amplitude hd μ) ≠ 0 ∧
      mean d (branchPotential hd (amplitude hd μ)) = 0 ∧
      SmoothOnTorus (branchPotential hd (amplitude hd μ)) ∧
      (∀ s : ℝ, InSobolev s (branchPotential hd (amplitude hd μ))) ∧
      ReducedEquation.full d μ (branchPotential hd (amplitude hd μ)) = 0 := by
  have hs := amplitude_spec hd ⟨hμ.le,hu⟩
  have hr := (localInterval hd).regular _ hs.1
  exact ⟨branchPotential_nonzero hd (amplitude_pos hd hμ hu).ne',branchPotential_mean hd _,
    hr.1,hr.2.1,by simpa only [hs.2] using hr.2.2⟩

theorem parameter_difference_onset_bound :
    (fun μ : ℝ => μ-1) =O[𝓝[>] (1:ℝ)] onset := by
  apply IsBigO.of_bound 2
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds] with μ hμ hu
  change 1 < μ at hμ
  have ho := onset_pos hμ
  have hm : μ ≠ 0 := by linarith
  rw [← onset_identity hm]
  simp only [norm_mul,Real.norm_eq_abs,abs_of_pos ho,abs_of_pos (by linarith : 0<μ)]
  exact mul_le_mul_of_nonneg_right hu.le ho.le

theorem amplitude_square_expansion {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => (amplitude hd μ)^2-onset μ/kappa d) =O[𝓝[>] (1:ℝ)]
      (fun μ => (onset μ)^2) := by
  have hfour : (fun μ => ‖amplitude hd μ‖^4) =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^2) := by
    convert (amplitude_square_bound hd).pow 2 using 1 <;> try rfl
    funext μ
    rw [Real.norm_eq_abs,abs_of_nonneg (amplitude_nonneg hd μ)]
    ring
  have hrem : (fun μ => μ-1-kappa d*(amplitude hd μ)^2) =O[𝓝[>] (1:ℝ)]
      (fun μ => (onset μ)^2) := by
    apply (((parameter_expansion hd).comp_tendsto (amplitude_tendsto hd)).trans hfour).congr'
    · filter_upwards [eventually_parameter_interval hd] with μ hi
      simp only [Function.comp_apply,(amplitude_spec hd hi).2]
    · exact Eventually.of_forall (fun _ => rfl)
  have hphys : (fun μ => μ-1-onset μ) =O[𝓝[>] (1:ℝ)] (fun μ => (onset μ)^2) := by
    have h := parameter_difference_onset_bound.mul (isBigO_refl onset (𝓝[>] (1:ℝ)))
    apply h.congr'
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      change 1 < μ at hμ
      have he := onset_identity (μ := μ) (by linarith)
      nlinarith
    · exact Eventually.of_forall (fun μ => by ring)
  have h := (hphys.sub hrem).const_mul_left (1/kappa d)
  apply h.congr_left
  intro μ
  have hk : kappa d ≠ 0 := (kappa_pos d hd).ne'
  field_simp
  <;> ring

/-- An error of order δ is already sufficient for the stated leading profile. -/
theorem amplitude_sqrt_bound {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => amplitude hd μ-Real.sqrt (onset μ/kappa d)) =O[𝓝[>] (1:ℝ)] onset := by
  obtain ⟨C,hC⟩ := (amplitude_square_expansion hd).exists_pos
  apply IsBigO.of_bound (Real.sqrt C)
  filter_upwards [hC.2.bound,self_mem_nhdsWithin] with μ hb hμ
  change 1 < μ at hμ
  have ho := onset_pos hμ
  have hk := kappa_pos d hd
  have ha := amplitude_nonneg hd μ
  have hs := Real.sqrt_nonneg (onset μ/kappa d)
  have hs2 := Real.sq_sqrt (div_nonneg ho.le hk.le)
  have hC0 := Real.sqrt_nonneg C
  have hC2 := Real.sq_sqrt hC.1.le
  simp only [Real.norm_eq_abs,abs_pow,abs_of_pos ho] at hb ⊢
  have hdiff : (amplitude hd μ-Real.sqrt (onset μ/kappa d))^2 ≤
      |(amplitude hd μ)^2-onset μ/kappa d| := by
    by_cases hh : Real.sqrt (onset μ/kappa d) ≤ amplitude hd μ
    · have hh' : 0 ≤ (amplitude hd μ)^2-onset μ/kappa d := by nlinarith
      rw [abs_of_nonneg hh']
      nlinarith
    · have hh' : (amplitude hd μ)^2-onset μ/kappa d ≤ 0 := by nlinarith
      rw [abs_of_nonpos hh']
      nlinarith
  have hbound := hdiff.trans hb
  have hprod : (Real.sqrt C*onset μ)^2 = C*(onset μ)^2 := by
    rw [mul_pow,hC2]
  have hnonneg : 0 ≤ Real.sqrt C*onset μ := mul_nonneg hC0 ho.le
  have habs := sq_abs (amplitude hd μ-Real.sqrt (onset μ/kappa d))
  nlinarith

/-- The actual continuous potential has the stated leading first-shell profile
with an error of order physical onset in the uniform norm. -/
theorem amplitude_potential_profile {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => branchPotential hd (amplitude hd μ) -
      assembly d (realDiagonal d (Real.sqrt (onset μ/kappa d))))
      =O[𝓝[>] (1:ℝ)] onset := by
  let L : ℝ →L[ℝ] Space d := (assembly d).comp (realDiagonal d)
  have hlin : (fun μ => L (amplitude hd μ-Real.sqrt (onset μ/kappa d)))
      =O[𝓝[>] (1:ℝ)] onset :=
    (L.isBigO_comp _ _).trans (amplitude_sqrt_bound hd)
  have hdiag : (fun μ => ‖realDiagonal d (amplitude hd μ)‖^2)
      =O[𝓝[>] (1:ℝ)] onset :=
    (((realDiagonal d).isBigO_comp (amplitude hd) (𝓝[>] (1:ℝ))).norm_left.pow 2).trans
      (amplitude_square_bound hd)
  have hcor : (fun μ => (GreenLocalBranch.correction hd
      (parameter hd (amplitude hd μ),realDiagonal d (amplitude hd μ)) : Space d))
      =O[𝓝[>] (1:ℝ)] onset :=
    ((UniformComplementBounds.correction_coe_uniform_quadratic hd).comp_tendsto
      ((branch_coordinates_tendsto hd).comp (amplitude_tendsto hd))).trans hdiag
  apply (hlin.add hcor).congr_left
  intro μ
  simp only [L,ContinuousLinearMap.comp_apply,map_sub,branchPotential,ReducedEquation.potential,
    ContinuousComplement.reconstruction_apply]
  abel

/-- Strong scalar amplitude error, written without fractional-power conventions. -/
theorem amplitude_sqrt_remainder {d : ℕ} (hd : 12 ≤ d) :
    (fun μ => amplitude hd μ-Real.sqrt (onset μ/kappa d)) =O[𝓝[>] (1:ℝ)]
      (fun μ => onset μ*Real.sqrt (onset μ)) := by
  obtain ⟨C,hC⟩ := (amplitude_square_expansion hd).exists_pos
  apply IsBigO.of_bound (C*Real.sqrt (kappa d))
  filter_upwards [hC.2.bound,self_mem_nhdsWithin] with μ hb hμ
  change 1 < μ at hμ
  have ho := onset_pos hμ
  have hk := kappa_pos d hd
  have ha := amplitude_nonneg hd μ
  have hs := Real.sqrt_nonneg (onset μ/kappa d)
  have hs2 := Real.sq_sqrt (div_nonneg ho.le hk.le)
  have hroot : 0 < Real.sqrt (onset μ) := Real.sqrt_pos.mpr ho
  have hkroot : 0 < Real.sqrt (kappa d) := Real.sqrt_pos.mpr hk
  have hfactor : Real.sqrt (onset μ/kappa d)*Real.sqrt (kappa d) = Real.sqrt (onset μ) := by
    rw [Real.sqrt_div ho.le,div_mul_cancel₀ _ hkroot.ne']
  have hmul : |amplitude hd μ-Real.sqrt (onset μ/kappa d)| * Real.sqrt (onset μ/kappa d) ≤
      |(amplitude hd μ)^2-onset μ/kappa d| := by
    have he : (amplitude hd μ)^2-onset μ/kappa d =
        (amplitude hd μ-Real.sqrt (onset μ/kappa d)) *
          (amplitude hd μ+Real.sqrt (onset μ/kappa d)) := by nlinarith
    rw [he,abs_mul,abs_of_nonneg (add_nonneg ha hs)]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) (abs_nonneg _)
  simp only [Real.norm_eq_abs,abs_pow,abs_of_pos ho] at hb
  have hbound := mul_le_mul_of_nonneg_right (hmul.trans hb) hkroot.le
  simp only [mul_assoc,hfactor] at hbound
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos ho,abs_of_pos hroot]
  apply le_of_mul_le_mul_right (a := Real.sqrt (onset μ)) (a0 := hroot)
  calc
    _ ≤ C*((onset μ)^2*Real.sqrt (kappa d)) := hbound
    _ = (C*Real.sqrt (kappa d)*onset μ)*(Real.sqrt (onset μ))^2 := by
      rw [Real.sq_sqrt ho.le]
      ring
    _ = _ := by ring

#print axioms amplitude_potential_profile
#print axioms amplitude_sqrt_remainder
#print axioms amplitude_square_expansion
#print axioms amplitude_sqrt_bound
#print axioms amplitude_tendsto
#print axioms amplitude_square_bound
end BecknerOnofri.HighDim.DiagonalScalarBranch
