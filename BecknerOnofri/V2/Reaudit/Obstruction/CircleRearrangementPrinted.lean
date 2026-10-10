module

public import BecknerOnofri.CircleLayerCakeIdentification
public import BecknerOnofri.CircleRearrangementL1Properties
public import BecknerOnofri.CircleRadialSuperlevels
public import BecknerOnofri.BilinearPolarizationIntegral

@[expose] public section

/-! # Row S011: `lem:circle-rearrangement`, as printed

The manuscript's Lemma (circle rearrangement): for a bounded, nonnegative circle kernel `q` that is
even and nonincreasing in geodesic distance and nonnegative `f, g ∈ L¹`, with symmetric decreasing
rearrangements `f*, g*`,
1. `∬ f(x) q(x-y) g(y) ≤ ∬ f*(x) q(x-y) g*(y)` (Riesz; printed proof: Burchard–Hajaiej, Theorem 2);
2. `f ≤ g` a.e. implies `f* ≤ g*` a.e.;
3. `‖f* - g*‖₁ ≤ ‖f - g‖₁`;
and (2), (3) are printed as consequences of the layer-cake representation: rearrangement replaces
each superlevel set by a centered arc of the same measure, any two centered arcs are nested, and
`‖f*-g*‖₁ = ∫₀^∞ |m{f>t} - m{g>t}| dt ≤ ‖f-g‖₁`.

The repository proves (1) for the circle by two-point polarization, Arzelà–Ascoli and an `L¹` limit
(`BecknerOnofri.PolarizationL1.IsRearrangementLimit.circle_pairing_le`); this file reuses that
theorem for (1) (the special case used in print, not the cited theorem for general `n`).  For (2) and
(3) it formalizes the printed layer-cake argument itself:

* `lintegral_enorm_sub_eq`: `∫ |h-k| = ∫_ℝ m{t<h, t≥k or t<k, t≥h} dt` (Tonelli on `x ↦ 1_{[min,max)}`);
* `radial_superlevel_ae_rank_ball` (reused): the superlevel sets of a radial decreasing function are
  centered arcs (rank balls) of the same measure as the superlevel sets of `f`;
* `measure_separating_rankBall`: two rank balls are nested, the measure of their symmetric
  difference is `|r₁ - r₂|`;
* `ofReal_abs_sub_le_measure_separating`: `|m A - m B| ≤ m (A Δ B)`.

"Symmetric decreasing rearrangement" is the usual a.e.-defined object: an a.e. radially nonincreasing
function (`AntitoneRadiusAE`) equimeasurable with `f` (`IsSymmDecrRearr`); it exists and is unique
up to null sets (`exists_symmDecrRearr`, `IsSymmDecrRearr.ae_unique`). -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Legacy.TorusEndpoint
open scoped ENNReal
namespace BecknerOnofri.V2.Reaudit.Obstruction
open BecknerOnofri.PolarizationL1 BecknerOnofri.DistributionLimit

/-! ## The printed notion of rearrangement -/

/-- `F` is a symmetric decreasing rearrangement of `f` on the circle `ℝ/ℤ` (Haar measure one):
`F` is equimeasurable with `f` and nonincreasing in the geodesic distance `‖x 0‖` to the origin
(almost everywhere; `‖-x‖ = ‖x‖` makes this also even). -/
structure IsSymmDecrRearr (f F : Torus 1 → ℝ) : Prop where
  identDistrib : IdentDistrib F f (torusMeasure 1) (torusMeasure 1)
  radial : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F

/-- Existence of the symmetric decreasing rearrangement of a nonnegative `L¹` function: the
layer-cake representative `x ↦ ∫₀^∞ 1[rank x < m{f>t}] dt`. -/
theorem exists_symmDecrRearr {f : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) :
    ∃ F, IsSymmDecrRearr f F :=
  have h := layer_toReal_isRearrangementLimit hf hf0
  ⟨_, ⟨h.identDistrib hf, h.radial⟩⟩

/-- Uniqueness up to null sets. -/
theorem IsSymmDecrRearr.ae_unique {f F G : Torus 1 → ℝ} (hF : IsSymmDecrRearr f F)
    (hG : IsSymmDecrRearr f G) : F =ᵐ[torusMeasure 1] G :=
  ae_eq_of_identDistrib_antitoneRadiusAE (hF.identDistrib.trans hG.identDistrib.symm)
    hF.radial hG.radial

/-- Every symmetric decreasing rearrangement is a limit of Lipschitz (polarization) rearrangements. -/
theorem IsSymmDecrRearr.isRearrangementLimit {f F : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1))
    (hF : IsSymmDecrRearr f F) : IsRearrangementLimit f F :=
  (rearrangeL1_spec f hf).congr
    (rearrangeL1_eq_of_radial_identDistrib hf hF.identDistrib hF.radial)

/-- ... and agrees a.e. with the layer-cake function. -/
theorem IsSymmDecrRearr.ae_eq_layer {f F : Torus 1 → ℝ} (hf : Integrable f (torusMeasure 1))
    (hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) (hF : IsSymmDecrRearr f F) :
    (fun x => (layerRearrangement f x).toReal) =ᵐ[torusMeasure 1] F :=
  (hF.isRearrangementLimit hf).layer_toReal_ae hf hf0

/-! ## Layer cake for the distance of two functions -/

/-- The set of heights `t` at which `t < a` and `t < b` disagree has length `|a - b|`. -/
lemma volume_separating (a b : ℝ) :
    volume {t : ℝ | ¬ (t < a ↔ t < b)} = ENNReal.ofReal |a - b| := by
  have key : ∀ {a b : ℝ}, a ≤ b → {t : ℝ | ¬ (t < a ↔ t < b)} = Ico a b := by
    intro a b hab
    ext t
    constructor
    · intro h
      by_cases ha : t < a
      · exact absurd ⟨fun _ => ha.trans_le hab, fun _ => ha⟩ h
      · refine ⟨not_lt.1 ha, ?_⟩
        by_contra hb
        exact h ⟨fun h' => absurd h' ha, fun h' => absurd h' hb⟩
    · rintro ⟨h1, h2⟩ hiff
      exact absurd (hiff.mpr h2) (not_lt.2 h1)
  rcases le_total a b with hab | hab
  · rw [key hab, Real.volume_Ico, abs_of_nonpos (sub_nonpos.2 hab), neg_sub]
  · have : {t : ℝ | ¬ (t < a ↔ t < b)} = {t : ℝ | ¬ (t < b ↔ t < a)} := by
      ext t; exact not_congr Iff.comm
    rw [this, key hab, Real.volume_Ico, abs_of_nonneg (sub_nonneg.2 hab)]

section LayerCake
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]

/-- `∫ |h - k| dμ = ∫_ℝ μ{x : t is between h x and k x} dt` (layer cake for the distance; both
sides in `[0, ∞]`). -/
lemma lintegral_enorm_sub_eq {h k : α → ℝ} (hh : Measurable h) (hk : Measurable k) :
    ∫⁻ x, ‖h x - k x‖ₑ ∂μ = ∫⁻ t : ℝ, μ {x | ¬ (t < h x ↔ t < k x)} := by
  set S : Set (α × ℝ) := {p | ¬ (p.2 < h p.1 ↔ p.2 < k p.1)} with hSdef
  have hS : MeasurableSet S := by
    refine MeasurableSet.compl ?_
    exact MeasurableSet.iff (measurableSet_lt measurable_snd (hh.comp measurable_fst))
      (measurableSet_lt measurable_snd (hk.comp measurable_fst))
  have h1 : ∀ x, ∫⁻ t : ℝ, S.indicator 1 (x, t) = ‖h x - k x‖ₑ := by
    intro x
    have hmeas : MeasurableSet {t : ℝ | ¬ (t < h x ↔ t < k x)} :=
      measurable_prodMk_left hS
    have : (fun t : ℝ => S.indicator (1 : α × ℝ → ℝ≥0∞) (x, t)) =
        {t : ℝ | ¬ (t < h x ↔ t < k x)}.indicator 1 := by
      funext t; simp [Set.indicator, hSdef]
    rw [this, lintegral_indicator_one hmeas, volume_separating, Real.enorm_eq_ofReal_abs]
  have h2 : ∀ t : ℝ, ∫⁻ x, S.indicator 1 (x, t) ∂μ = μ {x | ¬ (t < h x ↔ t < k x)} := by
    intro t
    have hmeas : MeasurableSet {x : α | ¬ (t < h x ↔ t < k x)} :=
      measurable_prodMk_right hS
    have : (fun x : α => S.indicator (1 : α × ℝ → ℝ≥0∞) (x, t)) =
        {x : α | ¬ (t < h x ↔ t < k x)}.indicator 1 := by
      funext x; simp [Set.indicator, hSdef]
    rw [this, lintegral_indicator_one hmeas]
  calc ∫⁻ x, ‖h x - k x‖ₑ ∂μ = ∫⁻ x, (∫⁻ t : ℝ, S.indicator 1 (x, t)) ∂μ :=
        lintegral_congr fun x => (h1 x).symm
    _ = ∫⁻ t : ℝ, (∫⁻ x, S.indicator 1 (x, t) ∂μ) := by
        apply lintegral_lintegral_swap
        exact (measurable_one.indicator hS).aemeasurable
    _ = _ := lintegral_congr h2

omit [SigmaFinite μ] in
/-- `|m A - m B| ≤ m (A Δ B)`, with `A Δ B` written as the set of points where membership
differs (no measurability needed). -/
lemma ofReal_abs_sub_le_measure_separating [IsFiniteMeasure μ] (A B : Set α) :
    ENNReal.ofReal |(μ A).toReal - (μ B).toReal| ≤ μ {x | ¬ (x ∈ A ↔ x ∈ B)} := by
  set D : Set α := {x | ¬ (x ∈ A ↔ x ∈ B)} with hD
  have hDfin : μ D ≠ ∞ := measure_ne_top _ _
  have hAB : μ A ≤ μ B + μ D := by
    calc μ A ≤ μ (B ∪ D) := by
          apply measure_mono
          intro x hx
          by_cases hxB : x ∈ B
          · exact Or.inl hxB
          · exact Or.inr (fun h => hxB (h.1 hx))
      _ ≤ μ B + μ D := measure_union_le _ _
  have hBA : μ B ≤ μ A + μ D := by
    calc μ B ≤ μ (A ∪ D) := by
          apply measure_mono
          intro x hx
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · exact Or.inr (fun h => hxA (h.2 hx))
      _ ≤ μ A + μ D := measure_union_le _ _
  have h1 : (μ A).toReal ≤ (μ B).toReal + (μ D).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hDfin⟩) hAB
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hDfin] at this
  have h2 : (μ B).toReal ≤ (μ A).toReal + (μ D).toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hDfin⟩) hBA
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hDfin] at this
  calc ENNReal.ofReal |(μ A).toReal - (μ B).toReal| ≤ ENNReal.ofReal (μ D).toReal :=
        ENNReal.ofReal_le_ofReal (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
    _ = μ D := ENNReal.ofReal_toReal hDfin

end LayerCake

/-! ## Centered arcs are nested -/

/-- Two centered arcs (rank balls) of measures `r₁, r₂ ∈ [0,1]` have symmetric difference of
measure `|r₁ - r₂|`; this is the nesting of centered arcs used in print. -/
lemma measure_separating_rankBall {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h1' : r₁ ≤ 1) (h2 : 0 ≤ r₂)
    (h2' : r₂ ≤ 1) :
    torusMeasure 1 {x | ¬ (circleRank x < r₁ ↔ circleRank x < r₂)} = ENNReal.ofReal |r₁ - r₂| := by
  have key : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ 1 →
      torusMeasure 1 {x | ¬ (circleRank x < a ↔ circleRank x < b)} = ENNReal.ofReal (b - a) := by
    intro a b ha hab hb
    have hset : {x : Torus 1 | ¬ (circleRank x < a ↔ circleRank x < b)} =
        {x | circleRank x < b} \ {x | circleRank x < a} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
      constructor
      · intro h
        by_cases hxa : circleRank x < a
        · exact absurd ⟨fun _ => hxa.trans_le hab, fun _ => hxa⟩ h
        · refine ⟨?_, hxa⟩
          by_contra hxb
          exact h ⟨fun h' => absurd h' hxa, fun h' => absurd h' hxb⟩
      · rintro ⟨hxb, hxa⟩ hiff
        exact hxa (hiff.mpr hxb)
    have hsub : {x : Torus 1 | circleRank x < a} ⊆ {x | circleRank x < b} :=
      fun x hx => lt_of_lt_of_le hx hab
    have hmeas : MeasurableSet {x : Torus 1 | circleRank x < a} :=
      (isOpen_lt circleRank_continuous continuous_const).measurableSet
    rw [hset, measure_sdiff hsub hmeas.nullMeasurableSet (measure_ne_top _ _),
      circleRank_sublevel_measure ha (hab.trans hb), circleRank_sublevel_measure (ha.trans hab) hb,
      ← ENNReal.ofReal_sub _ ha]
  rcases le_total r₁ r₂ with h | h
  · rw [key h1 h h2', abs_of_nonpos (sub_nonpos.2 h), neg_sub]
  · have hs : {x : Torus 1 | ¬ (circleRank x < r₁ ↔ circleRank x < r₂)} =
        {x | ¬ (circleRank x < r₂ ↔ circleRank x < r₁)} := by
      ext x; exact not_congr Iff.comm
    rw [hs, key h2 h h1', abs_of_nonneg (sub_nonneg.2 h)]

/-! ## The printed layer-cake argument for (2) and (3) -/

section Printed

lemma toReal_measure_mem_unit (s : Set (Torus 1)) :
    0 ≤ (torusMeasure 1 s).toReal ∧ (torusMeasure 1 s).toReal ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have : torusMeasure 1 s ≤ 1 := by
    simpa only [measure_univ] using measure_mono (μ := torusMeasure 1) (subset_univ s)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top this

/-- The printed contraction, in `[0,∞]` and for measurable representatives: the superlevel sets of
the rearrangements are nested centered arcs, so
`∫ |F-G| = ∫_ℝ |m{f>t} - m{g>t}| dt ≤ ∫_ℝ m({f>t} Δ {g>t}) dt = ∫ |f-g|`. -/
theorem lintegral_enorm_rearr_sub_le {f g F G : Torus 1 → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hFm : Measurable F) (hGm : Measurable G)
    (hF : IdentDistrib F f (torusMeasure 1) (torusMeasure 1))
    (hG : IdentDistrib G g (torusMeasure 1) (torusMeasure 1))
    (hFR : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) F)
    (hGR : AntitoneRadiusAE (torusMeasure 1) (fun x : Torus 1 => ‖x 0‖) G) :
    ∫⁻ x, ‖F x - G x‖ₑ ∂torusMeasure 1 ≤ ∫⁻ x, ‖f x - g x‖ₑ ∂torusMeasure 1 := by
  rw [lintegral_enorm_sub_eq hFm hGm, lintegral_enorm_sub_eq hfm hgm]
  refine lintegral_mono fun t => ?_
  have h1 := radial_superlevel_ae_rank_ball hFm.aemeasurable hFR t
  have h2 := radial_superlevel_ae_rank_ball hGm.aemeasurable hGR t
  have hFf : torusMeasure 1 {x | t < F x} = torusMeasure 1 {x | t < f x} :=
    hF.measure_mem_eq (s := Ioi t) measurableSet_Ioi
  have hGg : torusMeasure 1 {x | t < G x} = torusMeasure 1 {x | t < g x} :=
    hG.measure_mem_eq (s := Ioi t) measurableSet_Ioi
  have hae : {x | ¬ (t < F x ↔ t < G x)} =ᵐ[torusMeasure 1]
      {x | ¬ (circleRank x < (torusMeasure 1 {x | t < F x}).toReal ↔
        circleRank x < (torusMeasure 1 {x | t < G x}).toReal)} := by
    rw [Filter.eventuallyEq_set] at h1 h2 ⊢
    filter_upwards [h1, h2] with x hx1 hx2
    exact not_congr (iff_congr hx1 hx2)
  rw [measure_congr hae]
  obtain ⟨a1, a2⟩ := toReal_measure_mem_unit {x | t < F x}
  obtain ⟨b1, b2⟩ := toReal_measure_mem_unit {x | t < G x}
  rw [measure_separating_rankBall a1 a2 b1 b2, hFf, hGg]
  exact ofReal_abs_sub_le_measure_separating (μ := torusMeasure 1) {x | t < f x} {x | t < g x}

/-- Printed monotonicity: `f ≤ g` a.e. implies `f* ≤ g*` a.e.  Each superlevel set of `f*` is a
centered arc whose measure is at most that of the corresponding arc for `g*`; centered arcs are
nested; and countably many levels (the rationals) suffice. -/
theorem IsSymmDecrRearr.ae_le {f g F G : Torus 1 → ℝ} (hF : IsSymmDecrRearr f F)
    (hG : IsSymmDecrRearr g G) (hfg : f ≤ᵐ[torusMeasure 1] g) : F ≤ᵐ[torusMeasure 1] G := by
  have hlev : ∀ q : ℚ, ∀ᵐ x ∂torusMeasure 1, ((q : ℝ) < F x → (q : ℝ) < G x) := by
    intro q
    have h1 := radial_superlevel_ae_rank_ball hF.identDistrib.aemeasurable_fst hF.radial (q : ℝ)
    have h2 := radial_superlevel_ae_rank_ball hG.identDistrib.aemeasurable_fst hG.radial (q : ℝ)
    have hFf : torusMeasure 1 {x | (q : ℝ) < F x} = torusMeasure 1 {x | (q : ℝ) < f x} :=
      hF.identDistrib.measure_mem_eq (s := Ioi (q : ℝ)) measurableSet_Ioi
    have hGg : torusMeasure 1 {x | (q : ℝ) < G x} = torusMeasure 1 {x | (q : ℝ) < g x} :=
      hG.identDistrib.measure_mem_eq (s := Ioi (q : ℝ)) measurableSet_Ioi
    have hle : torusMeasure 1 {x | (q : ℝ) < F x} ≤ torusMeasure 1 {x | (q : ℝ) < G x} := by
      rw [hFf, hGg]
      apply measure_mono_ae
      filter_upwards [hfg] with x hx
      exact fun hq => hq.trans_le hx
    have hr : (torusMeasure 1 {x | (q : ℝ) < F x}).toReal ≤
        (torusMeasure 1 {x | (q : ℝ) < G x}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hle
    rw [Filter.eventuallyEq_set] at h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hF'
    exact hx2.mpr ((hx1.mp hF').trans_le hr)
  filter_upwards [ae_all_iff.2 hlev] with x hx
  by_contra hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (not_le.1 hlt)
  exact absurd (hx q hq2) (not_lt.2 hq1.le)

/-- Printed `L¹` contraction, for integrable `f, g` and any symmetric decreasing rearrangements. -/
theorem IsSymmDecrRearr.l1_contraction {f g F G : Torus 1 → ℝ}
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (hF : IsSymmDecrRearr f F) (hG : IsSymmDecrRearr g G) :
    (∫ x, |F x - G x| ∂torusMeasure 1) ≤ ∫ x, |f x - g x| ∂torusMeasure 1 := by
  -- pass to measurable representatives
  have hFa := hF.identDistrib.aemeasurable_fst
  have hGa := hG.identDistrib.aemeasurable_fst
  set f' := hf.aestronglyMeasurable.mk f with hf'
  set g' := hg.aestronglyMeasurable.mk g with hg'
  set F' := hFa.mk F with hF'
  set G' := hGa.mk G with hG'
  have ef : f =ᵐ[torusMeasure 1] f' := hf.aestronglyMeasurable.ae_eq_mk
  have eg : g =ᵐ[torusMeasure 1] g' := hg.aestronglyMeasurable.ae_eq_mk
  have eF : F =ᵐ[torusMeasure 1] F' := hFa.ae_eq_mk
  have eG : G =ᵐ[torusMeasure 1] G' := hGa.ae_eq_mk
  have mf : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have mg : Measurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have mF : Measurable F' := hFa.measurable_mk
  have mG : Measurable G' := hGa.measurable_mk
  have dF : IdentDistrib F' f' (torusMeasure 1) (torusMeasure 1) :=
    ((IdentDistrib.of_ae_eq mF.aemeasurable eF.symm).trans hF.identDistrib).trans
      (IdentDistrib.of_ae_eq hf.aemeasurable ef)
  have dG : IdentDistrib G' g' (torusMeasure 1) (torusMeasure 1) :=
    ((IdentDistrib.of_ae_eq mG.aemeasurable eG.symm).trans hG.identDistrib).trans
      (IdentDistrib.of_ae_eq hg.aemeasurable eg)
  have hmain := lintegral_enorm_rearr_sub_le mf mg mF mG dF dG
    (AntitoneRadiusAE.congr hF.radial eF) (AntitoneRadiusAE.congr hG.radial eG)
  have hlhs : ∫⁻ x, ‖F x - G x‖ₑ ∂torusMeasure 1 = ∫⁻ x, ‖F' x - G' x‖ₑ ∂torusMeasure 1 :=
    lintegral_congr_ae (by filter_upwards [eF, eG] with x h1 h2; rw [h1, h2])
  have hrhs : ∫⁻ x, ‖f x - g x‖ₑ ∂torusMeasure 1 = ∫⁻ x, ‖f' x - g' x‖ₑ ∂torusMeasure 1 :=
    lintegral_congr_ae (by filter_upwards [ef, eg] with x h1 h2; rw [h1, h2])
  have hfin : ∫⁻ x, ‖f x - g x‖ₑ ∂torusMeasure 1 ≠ ∞ := (hf.sub hg).2.ne
  have hle : ∫⁻ x, ‖F x - G x‖ₑ ∂torusMeasure 1 ≤ ∫⁻ x, ‖f x - g x‖ₑ ∂torusMeasure 1 := by
    rw [hlhs, hrhs]; exact hmain
  have hFG : AEStronglyMeasurable (fun x => F x - G x) (torusMeasure 1) :=
    (hFa.sub hGa).aestronglyMeasurable
  have e1 := integral_norm_eq_lintegral_enorm hFG
  have e2 := integral_norm_eq_lintegral_enorm (hf.sub hg).aestronglyMeasurable
  simp only [Pi.sub_apply, Real.norm_eq_abs] at e1 e2
  rw [e1, e2]
  exact ENNReal.toReal_mono hfin hle

end Printed

/-! ## The lemma as printed -/

/-- **`lem:circle-rearrangement`** (S011).  `q` bounded, nonnegative, even and nonincreasing in
geodesic distance (evenness is implied by `hq`, since `‖-x‖ = ‖x‖`); `f, g ≥ 0` in `L¹`;
`F, G` their symmetric decreasing rearrangements.  Then the Riesz inequality, the a.e. order
property and the `L¹` contraction hold.

Route: (1) is the repository's polarization/compactness proof of the circle Riesz inequality
(`IsRearrangementLimit.circle_pairing_le`; the manuscript cites Burchard–Hajaiej, Theorem 2);
(2) and (3) follow the printed layer-cake argument. -/
theorem circle_rearrangement_printed {f g F G : Torus 1 → ℝ}
    (hf : Integrable f (torusMeasure 1)) (hg : Integrable g (torusMeasure 1))
    (_hf0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ f x) (_hg0 : ∀ᵐ x ∂torusMeasure 1, 0 ≤ g x)
    (hF : IsSymmDecrRearr f F) (hG : IsSymmDecrRearr g G)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z, 0 ≤ q z) (hqC : ∀ z, q z ≤ C)
    (hq : ∀ x y, ‖x‖ ≤ ‖y‖ → q y ≤ q x) :
    (∫ p : Torus 1 × Torus 1, f p.1 * q (p.1 0 - p.2 0) * g p.2
        ∂(torusMeasure 1).prod (torusMeasure 1)) ≤
      (∫ p : Torus 1 × Torus 1, F p.1 * q (p.1 0 - p.2 0) * G p.2
        ∂(torusMeasure 1).prod (torusMeasure 1)) ∧
    (f ≤ᵐ[torusMeasure 1] g → F ≤ᵐ[torusMeasure 1] G) ∧
    (∫ x, |F x - G x| ∂torusMeasure 1) ≤ ∫ x, |f x - g x| ∂torusMeasure 1 := by
  refine ⟨?_, fun h => hF.ae_le hG h, hF.l1_contraction hf hg hG⟩
  have hC : ∀ z, ‖q z‖ ≤ C := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hq0 z)] using hqC z
  have h := (hF.isRearrangementLimit hf).circle_pairing_le (hG.isRearrangementLimit hg) hf hg q hC hq
  have e : ∀ u v : Torus 1 → ℝ,
      BilinearPolarization.pairing (fun x y : Torus 1 => q (x 0 - y 0)) u v =
        ∫ p : Torus 1 × Torus 1, u p.1 * q (p.1 0 - p.2 0) * v p.2
          ∂(torusMeasure 1).prod (torusMeasure 1) := by
    intro u v
    unfold BilinearPolarization.pairing BilinearPolarization.pairingIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  rw [← e, ← e]
  exact h

end BecknerOnofri.V2.Reaudit.Obstruction
