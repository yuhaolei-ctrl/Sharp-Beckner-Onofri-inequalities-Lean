module

public import BecknerOnofri.BinarySpinChannel
public import BecknerOnofri.EntropyShearer.PositiveBounds
public import BecknerOnofri.ConditionalMomentBounds
public import BecknerOnofri.V2.Channel.CircleFacts

@[expose] public section

/-!
# The all-minus cap by iterated monotonicity (work package G10, part (b))

Source: end of the proof of Proposition 5.12(i): the product arcsine law, the coordinatewise
nondecreasing functions `e^{V(C)}` and `-∏_i (1 - C_i)`, integration in one coordinate preserving
monotonicity in the remaining coordinates, and Chebyshev's association inequality applied
successively, giving
`∫ e^{V(C)} ∏_i (1-C_i) dm(C) ≤ ∫ e^{V(C)} dm(C)`; with the conditional spin probabilities
this is `ν_ρ(σ = -1,…,-1) = 2^{-12} ∫ e^{V(C)} ∏ (1 - C_i) dm ≤ 2^{-12}`
(`eq:section5-channel-all-minus`, `eq:section5-global-p0`).

Route remark.  The arcsine law is the law of `cos(2π x)` under normalized Haar measure on the
circle.  We keep the circle coordinates `x_i` (the product arcsine measure is the pushforward of
the product Haar measure under the cosine map) and phrase monotonicity in the cosine of each
coordinate.  Integrating out the coordinates `j ∈ T` one at a time is `EntropyShearer.avg`; the
one-dimensional Chebyshev inequality is `integral_mul_cos_nonneg`.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators
namespace BecknerOnofri.V2.Channel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.EntropyShearer BecknerOnofri.HighDim.Spin

/-- Monotone in the cosine of each coordinate, the other coordinates held fixed. -/
def CosMonotone {d : ℕ} (φ : Torus d → ℝ) : Prop :=
  ∀ (i : Fin d) (x : Torus d) (y z : UnitAddCircle), (fourier 1 y).re ≤ (fourier 1 z).re →
    φ (update x i y) ≤ φ (update x i z)

theorem bm_of_continuous {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f) :
    BoundedMeasurable f := by
  obtain ⟨B, hB⟩ := (isCompact_range hf.norm).bddAbove
  exact ⟨hf.measurable, B, fun x => hB (mem_range_self x)⟩

/-- Integrating out coordinate `j` against `1 - cos` can only decrease a monotone function
(coordinatewise Chebyshev). -/
theorem avg_mul_one_sub_cos_le {d : ℕ} {φ : Torus d → ℝ} (hφ : BoundedMeasurable φ)
    (hm : CosMonotone φ) (j : Fin d) (x : Torus d) :
    avg {j} (fun y => φ y * (1 - (fourier 1 (y j)).re)) x ≤ avg {j} φ x := by
  rw [avg_singleton, avg_singleton]
  simp only [Function.update_self]
  have hsec : Integrable (fun y : UnitAddCircle => φ (update x j y)) AddCircle.haarAddCircle :=
    ConditionalEntropy.section_integrable hφ j x
  have h0 := integral_mul_cos_nonneg hsec (fun y z h => hm j x y z h)
  have hi := integrable_mul_cosine hsec
  have : (fun z : UnitAddCircle => φ (update x j z) * (1 - (fourier 1 z).re)) =
      fun z => φ (update x j z) - φ (update x j z) * (fourier 1 z).re := by
    funext z; ring
  rw [this, integral_sub hsec hi]
  linarith

theorem CosMonotone.avg {d : ℕ} {φ : Torus d → ℝ} (hφ : BoundedMeasurable φ)
    (hm : CosMonotone φ) (j : Fin d) : CosMonotone (avg {j} φ) := by
  intro i x y z h
  rw [avg_singleton]
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_idem]
    exact le_rfl
  · have e : ∀ (w : UnitAddCircle) (u : UnitAddCircle),
        update (update x i u) j w = update (update x j w) i u :=
      fun w u => Function.update_comm hij _ _ _
    have hI : ∀ u : UnitAddCircle, Integrable (fun w : UnitAddCircle =>
        φ (update (update x j w) i u)) AddCircle.haarAddCircle := fun u => by
      have := ConditionalEntropy.section_integrable hφ j (update x i u)
      simpa only [e] using this
    simp only [e]
    exact integral_mono (hI y) (hI z) (fun w => hm i (update x j w) y z h)

/-- Core iteration: integrating `φ ∏_{i∈T}(1-cos x_i)` is at most integrating `φ`. -/
theorem integral_mul_prod_one_sub_cos_le {d : ℕ} (T : Finset (Fin d)) :
    ∀ φ : Torus d → ℝ, BoundedMeasurable φ → CosMonotone φ →
      (∫ x, φ x * ∏ i ∈ T, (1 - (fourier 1 (x i)).re) ∂torusMeasure d) ≤
        ∫ x, φ x ∂torusMeasure d := by
  induction T using Finset.induction_on with
  | empty => intro φ hφ hm; simp
  | insert j T hj ih =>
    intro φ hφ hm
    set g : Torus d → ℝ := fun x => ∏ i ∈ T, (1 - (fourier 1 (x i)).re) with hgdef
    have hcosx : ∀ i : Fin d, Continuous (fun x : Torus d => (fourier 1 (x i)).re) := fun i =>
      cosine_continuous.comp (continuous_apply i)
    have hg : Continuous g := continuous_finsetProd _ (fun i _ => continuous_const.sub (hcosx i))
    have hgb : BoundedMeasurable g := bm_of_continuous hg
    have hg0 : ∀ x, 0 ≤ g x := fun x => Finset.prod_nonneg (fun i _ =>
      sub_nonneg.mpr (abs_le.mp (CircleScalar.circle_cosine_bound (x i))).2)
    have hginv : ∀ x y, g (updateFinset x {j} y) = g x := by
      intro x y
      apply Finset.prod_congr rfl
      intro i hi
      have : i ∉ ({j} : Finset (Fin d)) := by
        simp only [Finset.mem_singleton]; rintro rfl; exact hj hi
      simp [updateFinset, this]
    have hf1 : BoundedMeasurable (fun x => φ x * (1 - (fourier 1 (x j)).re)) :=
      hφ.mul (bm_of_continuous (continuous_const.sub (hcosx j)))
    have hmono : CosMonotone (avg {j} φ) := CosMonotone.avg hφ hm j
    calc (∫ x, φ x * ∏ i ∈ insert j T, (1 - (fourier 1 (x i)).re) ∂torusMeasure d)
        = ∫ x, (φ x * (1 - (fourier 1 (x j)).re)) * g x ∂torusMeasure d := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Finset.prod_insert hj]
          simp only [hgdef]
          ring
      _ = ∫ x, avg {j} (fun y => φ y * (1 - (fourier 1 (y j)).re)) x * g x ∂torusMeasure d :=
          integral_pairing {j} hf1 hgb hginv
      _ ≤ ∫ x, avg {j} φ x * g x ∂torusMeasure d := by
          apply integral_mono
          · exact ((hf1.avg {j}).mul hgb).integrable
          · exact (((hφ.avg {j}).mul hgb)).integrable
          · intro x
            exact mul_le_mul_of_nonneg_right (avg_mul_one_sub_cos_le hφ hm j x) (hg0 x)
      _ ≤ ∫ x, avg {j} φ x ∂torusMeasure d := ih (avg {j} φ) (hφ.avg {j}) hmono
      _ = ∫ x, φ x ∂torusMeasure d := integral_avg {j} hφ

/-- The all-minus probability of the channel: `ν(σ ≡ -1) = 2^{-12} ∫ ρ ∏_i (1 - C_i)`. -/
theorem channelLaw_empty (ρ : ProbabilityDensity 12) :
    channelLaw ρ ∅ = (1 / 4096 : ℝ) *
      ∫ x, ρ.value x * ∏ i : Fin 12, (1 - (fourier 1 (x i)).re) ∂torusMeasure 12 := by
  unfold channelLaw
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [channel, Finset.prod_empty, Finset.compl_empty, one_mul, torusCosines]
  have : ∏ i : Fin 12, (1 - (fourier 1 (x i)).re) / 2 =
      (1 / 2) ^ 12 * ∏ i : Fin 12, (1 - (fourier 1 (x i)).re) := by
    rw [show (fun i : Fin 12 => (1 - (fourier 1 (x i)).re) / 2) =
      fun i => (1 / 2) * (1 - (fourier 1 (x i)).re) from funext fun i => by ring,
      Finset.prod_mul_distrib]
    simp
  rw [this]
  norm_num
  ring

/-- **All-minus cap** (`eq:section5-global-p0`): `ν_ρ(σ_1 = ⋯ = σ_12 = -1) ≤ 2^{-12}`
for every continuous probability density that is nondecreasing in the cosine of each coordinate. -/
theorem allMinus_le {ρ : ProbabilityDensity 12} (hcont : Continuous ρ.value)
    (hm : CosMonotone ρ.value) : channelLaw ρ ∅ ≤ 1 / 4096 := by
  rw [channelLaw_empty]
  have h := integral_mul_prod_one_sub_cos_le (Finset.univ : Finset (Fin 12)) ρ.value
    (bm_of_continuous hcont) hm
  rw [ρ.mass] at h
  calc (1 / 4096 : ℝ) * _ ≤ (1 / 4096 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 1 / 4096 := by ring

end BecknerOnofri.V2.Channel
