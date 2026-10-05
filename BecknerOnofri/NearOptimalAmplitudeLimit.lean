module

public import BecknerOnofri.LocalAmplitudeSelection
public import BecknerOnofri.RescaledAmplitudeUniqueness
public import BecknerOnofri.FirstShellOrbits

@[expose] public section

/-! Near-optimal actual energy forces normalized positive amplitudes to the
all-active limiting point, where the genuine rescaled implicit theorem applies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.NearOptimalAmplitudeLimit
open ContinuousFirstShell LocalReducedEnergyUpper ReducedEnergyGradient AmplitudeLinearization

def scale (d : ℕ) (μ : ℝ) : ℝ := Real.sqrt ((μ-1)/kappa d)

def normalizedAmplitudes {d : ℕ} (μ : ℝ) (z : Coordinates d) : Amplitudes d :=
  fun i => ‖z i‖/scale d μ

theorem scale_pos {d : ℕ} (hd : 12 ≤ d) {μ : ℝ} (hμ : 1<μ) : 0<scale d μ :=
  Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hμ) (kappa_pos d hd))

theorem scale_sq {d : ℕ} (hd : 12 ≤ d) {μ : ℝ} (hμ : 1≤μ) :
    (scale d μ)^2=(μ-1)/kappa d :=
  Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hμ) (kappa_pos d hd).le)

theorem scale_tendsto {d : ℕ} (hd : 12 ≤ d) {α : Type*} {l : Filter α} {μ : α → ℝ}
    (hμ : Tendsto μ l (𝓝 1)) : Tendsto (fun n => scale d (μ n)) l (𝓝 0) := by
  have ht := ((hμ.sub_const 1).div_const (kappa d)).sqrt
  simpa only [sub_self,zero_div,Real.sqrt_zero,scale] using ht

/-- Energy alone gives convergence of every normalized positive amplitude;
stationarity is not required until the subsequent orbit classification. -/
theorem normalizedAmplitudes_tendsto {d : ℕ} (hd : 12 ≤ d) {α : Type*} {l : Filter α}
    {μ : α → ℝ} {z : α → Coordinates d} (hμ : Tendsto μ l (𝓝 1)) (hz : Tendsto z l (𝓝 0))
    (hμpos : ∀ᶠ n in l, 1<μ n) (C₀ : ℝ) (hC₀ : 0≤C₀)
    (hE : ∀ᶠ n in l, 0≤physicalReducedEnergy hd (μ n,z n))
    (hlow : ∀ᶠ n in l,
      (d:ℝ)/(2*kappa d)*(onsetParameter (μ n))^2-C₀*(onsetParameter (μ n))^3 ≤
        physicalReducedEnergy hd (μ n,z n)) :
    Tendsto (fun n => normalizedAmplitudes (μ n) (z n)) l (𝓝 (fun _ => 1)) := by
  obtain ⟨C,hC,hbound⟩ := near_optimal_amplitude_bound hd C₀ hC₀
  have hpair := hμ.prodMk_nhds hz
  have hδ : Tendsto (fun n => onsetParameter (μ n)) l (𝓝 0) := onsetParameter_tendsto.comp hpair
  have hsum : ∀ᶠ n in l,
      (∑ i : Fin d, (‖z n i‖^2-onsetParameter (μ n)/kappa d)^2) ≤ C*(onsetParameter (μ n))^3 := by
    filter_upwards [hpair.eventually hbound,hμpos,hE,hlow] with n hb hp he hl
    exact hb hp he hl
  apply tendsto_pi_nhds.mpr
  intro i
  have hsmall : ∀ᶠ n in l,
      ‖‖z n i‖^2/onsetParameter (μ n)-1/kappa d‖ ≤ Real.sqrt (C*onsetParameter (μ n)) := by
    filter_upwards [hsum,hμpos] with n hs hp
    have hδp := onsetParameter_pos hp
    have hk := kappa_pos d hd
    have hi : (‖z n i‖^2-onsetParameter (μ n)/kappa d)^2 ≤
        C*(onsetParameter (μ n))^3 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (‖z n j‖^2-onsetParameter (μ n)/kappa d))
        (Finset.mem_univ i)).trans hs
    have he : (‖z n i‖^2/onsetParameter (μ n)-1/kappa d)^2*(onsetParameter (μ n))^2 =
        (‖z n i‖^2-onsetParameter (μ n)/kappa d)^2 := by
      field_simp
      <;> ring
    have hq : (‖z n i‖^2/onsetParameter (μ n)-1/kappa d)^2 ≤ C*onsetParameter (μ n) := by
      apply le_of_mul_le_mul_right (a := (onsetParameter (μ n))^2) (a0 := sq_pos_of_pos hδp)
      rw [he]
      nlinarith [hi]
    simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt hq
  have hroot : Tendsto (fun n => Real.sqrt (C*onsetParameter (μ n))) l (𝓝 0) := by
    simpa only [mul_zero,Real.sqrt_zero] using (hδ.const_mul C).sqrt
  have hzero := squeeze_zero_norm' hsmall hroot
  have hratio : Tendsto (fun n => ‖z n i‖^2/onsetParameter (μ n)) l (𝓝 (1/kappa d)) := by
    convert hzero.add_const (1/kappa d) using 1 <;> simp
  have hsq : Tendsto (fun n => ‖z n i‖^2/(scale d (μ n))^2) l (𝓝 1) := by
    have ht0 : Tendsto (fun n => kappa d/μ n) l (𝓝 (kappa d)) := by
      convert ((tendsto_const_nhds : Tendsto (fun _ : α => kappa d) l (𝓝 (kappa d))).div
        hμ (by norm_num : (1:ℝ)≠0)) using 1 <;> first | rfl | simp
    have ht := ht0.mul hratio
    have hk := kappa_pos d hd
    have heq : ∀ᶠ n in l, (kappa d/μ n)*(‖z n i‖^2/onsetParameter (μ n)) =
        ‖z n i‖^2/(scale d (μ n))^2 := by
      filter_upwards [hμpos] with n hn
      have hm : μ n ≠ 0 := by linarith
      have hδp := onsetParameter_pos hn
      rw [scale_sq hd hn.le]
      unfold onsetParameter
      field_simp
    convert (Tendsto.congr' heq ht) using 1 <;> simp [hk.ne']
  have h := hsq.sqrt
  have heq : (fun n => Real.sqrt (‖z n i‖^2/(scale d (μ n))^2)) =
      (fun n => normalizedAmplitudes (μ n) (z n) i) := by
    funext n
    have hs : 0 ≤ scale d (μ n) := Real.sqrt_nonneg _
    rw [← div_pow,Real.sqrt_sq_eq_abs,abs_of_nonneg (div_nonneg (norm_nonneg _) hs)]
    rfl
  simpa only [heq,Real.sqrt_one] using h

#print axioms normalizedAmplitudes_tendsto
end BecknerOnofri.HighDim.NearOptimalAmplitudeLimit
