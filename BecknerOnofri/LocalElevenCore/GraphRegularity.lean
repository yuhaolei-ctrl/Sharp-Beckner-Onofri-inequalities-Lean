import BecknerOnofri.LocalElevenContinuousInverse
import BecknerOnofri.QuarticSignsEleven
import BecknerOnofri.GraphRegularity
import BecknerOnofri.LocalElevenCore.GraphCritical
import BecknerOnofri.OnsetRaw

/-! Arbitrary continuous solutions of the actual complementary Gibbs equation
have all polynomial Wiener moments and are smooth in every Sobolev space.
The unsolved first shell contributes only finitely many Fourier coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace BecknerOnofri.HighDim.LocalEleven.GraphRegularity

open BecknerOnofri.HighDim.GraphRegularity hiding Radial green_radial_step green_radial_zero inSobolev_of_radial normalized_coefficient_legacy normalized_radial potential_regular radial_of_same_complement radial_smul reconstruction_radial reconstruction_regular same_complement_of_projected smooth_of_radial toL2_real
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation

open Legacy.TorusEndpoint

open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.RadialWiener

/-- Actual continuous Fourier coefficients with an absolutely summable radial moment. -/
def Radial {d : ℕ} (m : ℕ) (u : ContinuousGibbs.Space d) : Prop :=
  RadialSummable (fun k => coefficient k u) m

theorem radial_of_same_complement {d : ℕ} (m : ℕ) (f g : ContinuousGibbs.Space d)
    (hg : Radial m g)
    (he : ∀ k : Frequency d, ComplementFrequency k → coefficient k g = coefficient k f) :
    Radial m f := by
  apply hg.congr_cofinite
  have hs : Set.Finite {k : Frequency d | k = 0 ∨ InFirstShell k} :=
    (Set.finite_singleton 0).union (GraphCritical.firstShell_finite d)
  filter_upwards [hs.compl_mem_cofinite] with k hk
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or] at hk
  rw [he k hk]

theorem radial_smul {d : ℕ} (m : ℕ) (c : ℝ) (u : ContinuousGibbs.Space d) (hu : Radial m u) :
    Radial m (c • u) := by
  apply (hu.mul_left ‖c‖).congr
  intro k
  simp only [map_smul, norm_smul]
  ring

/-- Cauchy–Schwarz pairs the actual Green ℓ² multiplier with the Fourier ℓ² data. -/
theorem green_radial_zero {d : ℕ} (hd : 0 < d) (u : ContinuousGibbs.Space d) :
    Radial 0 (greenContinuous d u) := by
  rw [Radial, radialSummable_zero]
  apply (green_series_summable d (continuousFourier d u)).congr
  intro k
  rw [greenFourierVector_apply hd, continuousFourier_apply, coefficient_green hd]

/-- The genuine Green multiplier gains d radial orders. -/
theorem green_radial_step {d : ℕ} (hd : 0 < d) (u : ContinuousGibbs.Space d)
    (m : ℕ) (hu : Radial m u) : Radial (m+d) (greenContinuous d u) := by
  apply elliptic_step (c := 1) (b := fun k => coefficient k u) (by norm_num)
  · rw [coefficient_zero, ReducedEquation.mean_green hd]
    simp
  · intro k hk
    rw [coefficient_green hd, if_neg hk, Bridge.frequencyLength_eq]
    have hr : (frequencyRadius k : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (frequencyRadius_pos hk).ne'
    push_cast
    field_simp
  · exact hu

theorem toL2_real {d : ℕ} (u : ContinuousGibbs.Space d) :
    Legacy.BecknerOnofri.SubcriticalAttainment.RealPotential (toL2 d u) := by
  filter_upwards [toL2_ae u] with x hx
  simp [hx]

/-- The actual continuous normalization agrees coefficientwise with the
normalization of its L² representative; null-set representatives do not matter. -/
theorem normalized_coefficient_legacy {d : ℕ} (u : ContinuousGibbs.Space d) (k : Frequency d) :
    coefficient k (normalized u) = Legacy.TorusEndpoint.densityFourier
      (fun x => Real.exp ((toL2 d u) x).re / partition u) k := by
  rw [coefficient_integral]
  apply integral_congr_ae
  filter_upwards [toL2_ae u] with x hx
  rw [hx]
  simp only [Complex.ofReal_re, normalized, ContinuousMap.smul_apply, smul_eq_mul,
    exponential_apply, div_eq_mul_inv]
  push_cast
  ring

theorem normalized_radial {d : ℕ} (u : ContinuousGibbs.Space d) (m : ℕ) (hu : Radial m u) :
    Radial m (normalized u) := by
  have h := gibbs_radialSummable (toL2 d u) m hu (toL2_real u) (partition u)
  apply h.congr
  intro k
  dsimp only
  rw [normalized_coefficient_legacy]

/-- The unsolved first shell is the only difference from the full Green equation. -/
theorem same_complement_of_projected {d : ℕ} (hd : 0 < d)
    (μ : ℝ) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0)
    (k : Frequency d) (hk : ComplementFrequency k) :
    coefficient k (μ • greenContinuous d (normalized (reconstruction d (z,w)))) =
      coefficient k (reconstruction d (z,w)) := by
  let f := normalized (reconstruction d (z,w)) - 1
  have hw : w = μ • complementMap d (greenContinuous d f) := sub_eq_zero.mp he
  have hz : coefficient k (assembly d z) = 0 := by
    rw [← projection_assembly z]
    exact coefficient_projection_off_shell _ k hk.2
  have hwc : coefficient k (w : ContinuousGibbs.Space d) = μ • coefficient k (greenContinuous d f) := by
    have h := congrArg (fun v : complement d => coefficient k (v : ContinuousGibbs.Space d)) hw
    simpa only [Submodule.coe_smul, map_smul, QuadraticModes.complementMap_coefficient, if_pos hk] using h
  have h1 : coefficient k (1 : ContinuousGibbs.Space d) = 0 := by
    change coefficient k (ContinuousMap.const (Torus d) 1) = 0
    rw [coefficient_const, if_neg hk.1]
  simp only [map_smul, reconstruction_apply, map_add, hz, zero_add, hwc,
    coefficient_green hd, f, map_sub, h1, mul_zero, sub_zero]

/-- Polynomial moments follow for arbitrary real μ, with no maximizer or
finite-dimensional Euler equation hypothesis. -/
theorem reconstruction_radial {d : ℕ} (hd : 0 < d)
    (μ : ℝ) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (m : ℕ) :
    Radial m (reconstruction d (z,w)) := by
  have hmultiple (n : ℕ) : Radial (n*d) (reconstruction d (z,w)) := by
    induction n with
    | zero =>
      rw [Nat.zero_mul]
      exact radial_of_same_complement 0 _ _
        (radial_smul 0 μ _ (green_radial_zero hd _))
        (same_complement_of_projected hd μ z w he)
    | succ n ih =>
      rw [Nat.succ_mul]
      exact radial_of_same_complement (n*d+d) _ _
        (radial_smul _ μ _ (green_radial_step hd _ (n*d) (normalized_radial _ _ ih)))
        (same_complement_of_projected hd μ z w he)
  exact radialSummable_mono (Nat.le_mul_of_pos_right m hd) (hmultiple m)

/-- Radial moments yield actual membership in the physical, 2π-normalized Sobolev spaces. -/
theorem inSobolev_of_radial {d : ℕ} (u : ContinuousGibbs.Space d)
    (hu : ∀ m : ℕ, Radial m u) (s : ℝ) : InSobolev s u := by
  obtain ⟨m, hm⟩ := exists_nat_ge s
  have h := BecknerOnofri.OnsetSobolev.realValue_mem_sobolev (toL2 d u) (toL2_real u) hm (hu (2*m))
  apply (OnsetRaw.inSobolev_congr_ae (u := RawAttainment.realValue (toL2 d u)) (v := u) ?_).mp h
  filter_upwards [toL2_ae u] with x hx
  simp only [RawAttainment.realValue, hx, Complex.ofReal_re]

/-- Polynomially summable actual Fourier moments make the actual continuous
representative smooth, rather than merely producing an unrelated a.e. version. -/
theorem smooth_of_radial {d : ℕ} (u : ContinuousGibbs.Space d)
    (hu : ∀ m : ℕ, Radial m u) : SmoothOnTorus u := by
  let a : Frequency d → ℂ := fun k => coefficient k u
  have hs : Summable (fun k => ‖fourierIsometry d (toL2 d u) k‖) :=
    (radialSummable_zero _).mp (hu 0)
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  haveI : (Legacy.TorusEndpoint.torusMeasure d).IsOpenPosMeasure := by
    rw [Legacy.TorusEndpoint.torusMeasure_explicit]
    infer_instance
  have he : Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) = fun x => (u x : ℂ) :=
    Measure.eq_of_ae_eq
      ((Legacy.BecknerOnofri.WienerFourier.representative_ae_eq (toL2 d u) hs).trans (toL2_ae u))
      (Legacy.BecknerOnofri.WienerFourier.representative_continuous (toL2 d u) hs)
      (Complex.continuous_ofReal.comp u.continuous)
  have h := Complex.reCLM.contDiff.comp
    (Legacy.BecknerOnofri.SmoothFourier.series_contDiff a hu)
  change ContDiff ℝ ∞ (fun x : Fin d → ℝ => u (Legacy.BecknerOnofri.SmoothFourier.quotient x))
  have he' (x : Fin d → ℝ) :
      (Legacy.TorusEndpoint.absoluteFourierSeries a (Legacy.BecknerOnofri.SmoothFourier.quotient x)).re =
        u (Legacy.BecknerOnofri.SmoothFourier.quotient x) := by
    change (Legacy.BecknerOnofri.WienerFourier.representative (toL2 d u) _).re = _
    rw [he, Complex.ofReal_re]
  simpa only [Function.comp_def, Complex.reCLM_apply, he'] using h

theorem reconstruction_regular {d : ℕ} (hd : 0 < d)
    (μ : ℝ) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    SmoothOnTorus (reconstruction d (z,w)) ∧
      ∀ s : ℝ, InSobolev s (reconstruction d (z,w)) := by
  have h := reconstruction_radial hd μ z w he
  exact ⟨smooth_of_radial _ h, inSobolev_of_radial _ h⟩

/-- Every nearby point on the actual local complementary graph is smooth and
belongs to every Sobolev space, without solving the reduced equation. -/
theorem potential_regular {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      SmoothOnTorus (potential hd x) ∧ ∀ s : ℝ, InSobolev s (potential hd x) := by
  filter_upwards [correction_solves hd] with x hx
  exact reconstruction_regular (by omega) x.1 x.2 (correction hd x) hx

#print axioms reconstruction_radial
#print axioms reconstruction_regular
#print axioms potential_regular
end BecknerOnofri.HighDim.LocalEleven.GraphRegularity
