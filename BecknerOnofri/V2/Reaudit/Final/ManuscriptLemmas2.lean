module

public import BecknerOnofri.V2.Reaudit.Final.All
public import BecknerOnofri.VariationalExtendedConvexity
public import BecknerOnofri.VariationalThresholdGeometry
public import BecknerOnofri.CircleLipschitzRearrangement
public import BecknerOnofri.CircleRearrangementL1Properties
public import BecknerOnofri.CircleRadialKernel
public import BecknerOnofri.V2.Reaudit.Obstruction.CircleRearrangementPrinted
public import BecknerOnofri.V2.Vocab.HomEntropy
public import BecknerOnofri.ClosedCubeTaylor
public import BecknerOnofri.V2.Reaudit.HeatKernel.PositiveBernstein
public import BecknerOnofri.V2.Reaudit.Mixtures.DirectTransfer
public import BecknerOnofri.V2.Reaudit.Obstruction.UniversalObstructions
public import BecknerOnofri.V2.Reaudit.SpinChannel.WrittenEndpoint
public import BecknerOnofri.V2.Circle.Psi
public import BecknerOnofri.V2.Assembly.LargeMean

@[expose] public section

/-! # Printed Section 2--5 statements as roots, second batch (Reaudit, Final)

Leaf module (imports `Final.All`; no forbidden endpoint module is added to its import closure beyond
those `Final.All` already imports).  Each root states the printed assertion exactly and is proved from
the route declarations named below, so that those declarations become ancestors of a root.

* S007 (`prop:section2-basic-curve-geometry`): `prop_section2_basic_curve_geometry`;
* S011 (`lem:circle-rearrangement`, `eq:circle-rearr-lipschitz`): `lem_circle_rearrangement_printed_full`,
  `eq_circle_rearr_lipschitz`;
* U01 (`eq:section2-relative-entropy`): `eq_section2_relative_entropy_printed`;
* S014 (`lem:positive-bernstein`): `lem_positive_bernstein_printed`,
  `lem_positive_bernstein_tensor_route`;
* S037 (`prop:spectral-marginal-energy`): `prop_spectral_marginal_energy_printed`;
* S040 (`cor:section5-high-endpoint`): `cor_section5_high_endpoint_printed`;
* S044 (`prop:section5-spin-entropy`, the properties of `ψ`): `prop_section5_psi_properties`. -/

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology NNReal BoundedContinuousFunction

namespace BecknerOnofri
open HighDim
open V2.Vocab

namespace V2.Reaudit.Final

/-! ## Row S007: `prop:section2-basic-curve-geometry`

The positivity of `β_gm` is the printed positive-threshold input (`section2_globalTransition_pos`
route, `ExternalInputs.positiveThreshold_independent_print`).  The coefficient-zero-set and the
threshold lower bounds are the proofs of `VariationalCurves.coefficient_zero_iff` and
`VariationalCurves.coefficient_lower_bounds`, with the positivity of `β_gm` supplied by this input
instead of `VariationalCurves.transition_positive` (whose proof goes through
`LowDimension.pressure_formula` and the forbidden module `Legacy.BecknerOnofri.EndpointThroughTen`). -/

/-- `β_gm(d) > 0`, from the positive-threshold input (independent of the low-dimensional endpoint). -/
theorem globalTransition_pos_printed {d : ℕ} (hd : 0 < d) :
    0 < VariationalCurves.globalTransition d :=
  V2.Vocab.globalTransition_pos_of_input hd (ExternalInputs.positiveThreshold_independent_print hd)

/-- `C_d(A) = 0 ⇔ A ≥ A₀(d)` (`eq:section2-defect-zero-set`): the proof of
`VariationalCurves.coefficient_zero_iff`, with `β_gm > 0` from the positive-threshold input. -/
theorem coefficient_zero_iff_printed {d : ℕ} (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    coefficientDefect d A = 0 ↔ VariationalCurves.zeroDefectCoefficient d ≤ A := by
  have hσ := spectralThreshold_pos hd
  have hT := globalTransition_pos_printed hd
  have hp : 0 < (2*Real.pi)^d := by positivity
  let β := spectralThreshold d/(2*A*(2*Real.pi)^d)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hc : spectralThreshold d/(2*β*(2*Real.pi)^d) = A := by dsimp [β]; field_simp
  rw [← hc, ← pressure_eq_coefficientDefect hd hβ, VariationalCurves.pressure_zero_iff hd]
  rw [hc]
  change spectralThreshold d/(2*A*(2*Real.pi)^d) ≤ VariationalCurves.globalTransition d ↔
    spectralThreshold d/(2*VariationalCurves.globalTransition d*(2*Real.pi)^d) ≤ A
  rw [div_le_iff₀ (by positivity : 0 < 2*A*(2*Real.pi)^d),
    div_le_iff₀ (by positivity : 0 < 2*VariationalCurves.globalTransition d*(2*Real.pi)^d)]
  constructor <;> intro h <;> nlinarith

/-- `β_gm(d) ≤ min{β_c(d), β_s(d)}` (first half of `eq:section2-threshold-upper-bounds`), as in the print:
`lem:section2-universal-obstructions` gives `P_d = +∞` beyond `2d` and `P_d > 0` beyond `β_s(d)`, while
`P_d(β_gm) = 0`. -/
theorem transition_upper_bounds_printed {d : ℕ} (hd : 0 < d) :
    VariationalCurves.globalTransition d ≤ min (2*(d:ℝ)) (spectralThreshold d) := by
  have hU := Obstruction.universal_obstructions hd
  have hz : pressure d (VariationalCurves.globalTransition d) = 0 :=
    (VariationalCurves.pressure_zero_iff hd _).mpr le_rfl
  refine le_min ?_ ?_
  · by_contra hn
    have h := hU.1 _ (lt_of_not_ge hn)
    rw [hz] at h
    exact (by simp : (0 : EReal) ≠ ⊤) h
  · by_contra hn
    have h := hU.2.2.2.1 _ (lt_of_not_ge hn)
    rw [hz] at h
    exact lt_irrefl _ h

/-- `A₀(d) ≥ max{A_crit(d), A_s(d)}` (second half of `eq:section2-threshold-upper-bounds`): the proof
of `VariationalCurves.coefficient_lower_bounds` with `β_gm > 0` from the positive-threshold input and
the first half `β_gm ≤ min{β_c, β_s}` from `transition_upper_bounds_printed`. -/
theorem coefficient_lower_bounds_printed {d : ℕ} (hd : 0 < d) :
    max (collapseCoefficient d) (spectralCoefficient d) ≤ VariationalCurves.zeroDefectCoefficient d := by
  have hσ := spectralThreshold_pos hd
  have hT := globalTransition_pos_printed hd
  have hp : 0 < (2*Real.pi)^d := by positivity
  have hb := transition_upper_bounds_printed hd
  have hc := hb.trans (min_le_left _ _)
  have hs := hb.trans (min_le_right _ _)
  apply max_le
  · unfold collapseCoefficient VariationalCurves.zeroDefectCoefficient
    apply div_le_div_of_nonneg_left hσ.le (by positivity)
    nlinarith
  · have he : spectralCoefficient d = spectralThreshold d/(2*spectralThreshold d*(2*Real.pi)^d) := by
      unfold spectralCoefficient
      field_simp
    rw [he]
    unfold VariationalCurves.zeroDefectCoefficient
    apply div_le_div_of_nonneg_left hσ.le (by positivity)
    nlinarith

/-- **`prop:section2-basic-curve-geometry`** (row S007), every assertion, for every `d ≥ 1`:
`P_d` is convex, nondecreasing and nonnegative on `[0, 2d]`; `C_d` is convex, nonincreasing and
nonnegative on `(0, ∞)`; `β_gm(d)` is the infimum of the entropy/interaction quotients over the
non-uniform finite-entropy densities; `P_d(β) = 0 ⇔ 0 ≤ β ≤ β_gm(d)`; `C_d(A) = 0 ⇔ A ≥ A₀(d)`;
`β_gm ≤ min{β_c, β_s}` and `A₀ ≥ max{A_crit, A_s}`. -/
theorem prop_section2_basic_curve_geometry {d : ℕ} (hd : 0 < d) :
    (MonotoneOn (pressure d) (Set.Icc 0 (2*(d:ℝ))) ∧
      (∀ β ∈ Set.Icc (0:ℝ) (2*(d:ℝ)), 0 ≤ pressure d β) ∧
      ∀ β ∈ Set.Icc (0:ℝ) (2*(d:ℝ)), ∀ γ ∈ Set.Icc (0:ℝ) (2*(d:ℝ)),
        ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
          pressure d (a*β+b*γ) ≤ (a:EReal)*pressure d β+(b:EReal)*pressure d γ) ∧
    (AntitoneOn (coefficientDefect d) (Set.Ioi 0) ∧
      (∀ A ∈ Set.Ioi (0:ℝ), 0 ≤ coefficientDefect d A) ∧
      ∀ A ∈ Set.Ioi (0:ℝ), ∀ B ∈ Set.Ioi (0:ℝ), ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a+b=1 →
        coefficientDefect d (a*A+b*B) ≤
          (a:EReal)*coefficientDefect d A+(b:EReal)*coefficientDefect d B) ∧
    VariationalCurves.globalTransition d =
      sInf (VariationalCurves.entropyInteractionQuotients d) ∧
    (∀ β : ℝ, 0 ≤ β → (pressure d β = 0 ↔ β ≤ VariationalCurves.globalTransition d)) ∧
    (∀ A : ℝ, 0 < A → (coefficientDefect d A = 0 ↔ VariationalCurves.zeroDefectCoefficient d ≤ A)) ∧
    VariationalCurves.globalTransition d ≤ min (2*(d:ℝ)) (spectralThreshold d) ∧
    max (collapseCoefficient d) (spectralCoefficient d) ≤ VariationalCurves.zeroDefectCoefficient d :=
  ⟨⟨(VariationalCurves.pressure_monotone hd).monotoneOn _,
      fun β _ => HighDim.pressure_nonneg d β,
      fun β _ γ _ a b ha hb hab => VariationalCurves.pressure_convex_combination hd β γ a b ha hb hab⟩,
    ⟨(HighDim.coefficientDefect_antitone hd).antitoneOn _,
      fun A _ => HighDim.coefficientDefect_nonneg d A,
      fun A _ B _ a b ha hb hab =>
        VariationalCurves.coefficient_convex_combination hd A B a b ha hb hab⟩,
    VariationalCurves.transition_quotient hd,
    fun β _ => VariationalCurves.pressure_zero_iff hd β,
    fun _ hA => coefficient_zero_iff_printed hd hA,
    transition_upper_bounds_printed hd,
    coefficient_lower_bounds_printed hd⟩

/-! ## Row S011: `lem:circle-rearrangement` -/

open BecknerOnofri.V2.Reaudit.Obstruction in
/-- **`lem:circle-rearrangement`** (row S011), all three assertions of the printed lemma: the Riesz
inequality (`eq:circle-rearrangement`), `f ≤ g` a.e. `⇒ f* ≤ g*` a.e., and
`‖f* - g*‖₁ ≤ ‖f - g‖₁`.  All three come from `circle_rearrangement_printed`; the order assertion is the layer-cake argument
`IsSymmDecrRearr.ae_le` (Step 2 of the printed proof). -/
theorem lem_circle_rearrangement_printed_full {f g F G : Legacy.TorusEndpoint.Torus 1 → ℝ}
    (hf : Integrable f (Legacy.TorusEndpoint.torusMeasure 1)) (hg : Integrable g (Legacy.TorusEndpoint.torusMeasure 1))
    (hf0 : ∀ᵐ x ∂Legacy.TorusEndpoint.torusMeasure 1, 0 ≤ f x) (hg0 : ∀ᵐ x ∂Legacy.TorusEndpoint.torusMeasure 1, 0 ≤ g x)
    (hF : IsSymmDecrRearr f F) (hG : IsSymmDecrRearr g G)
    (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z, 0 ≤ q z) (hqC : ∀ z, q z ≤ C)
    (hq : ∀ x y, ‖x‖ ≤ ‖y‖ → q y ≤ q x) :
    (∫ p : Legacy.TorusEndpoint.Torus 1 × Legacy.TorusEndpoint.Torus 1, f p.1 * q (p.1 0 - p.2 0) * g p.2
        ∂(Legacy.TorusEndpoint.torusMeasure 1).prod (Legacy.TorusEndpoint.torusMeasure 1)) ≤
      (∫ p : Legacy.TorusEndpoint.Torus 1 × Legacy.TorusEndpoint.Torus 1, F p.1 * q (p.1 0 - p.2 0) * G p.2
        ∂(Legacy.TorusEndpoint.torusMeasure 1).prod (Legacy.TorusEndpoint.torusMeasure 1)) ∧
    (f ≤ᵐ[Legacy.TorusEndpoint.torusMeasure 1] g → F ≤ᵐ[Legacy.TorusEndpoint.torusMeasure 1] G) ∧
    (∫ x, |F x - G x| ∂Legacy.TorusEndpoint.torusMeasure 1) ≤ ∫ x, |f x - g x| ∂Legacy.TorusEndpoint.torusMeasure 1 := by
  have h := circle_rearrangement_printed hf hg hf0 hg0 hF hG q hq0 hqC hq
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **`lem:circle-rearrangement`**: the symmetric decreasing rearrangement of an integrable function on the
circle is unique up to null sets (Step 1 of the printed proof: superlevel sets are centered arcs) and
exists (Step 5 of the printed proof: the `L¹` limit of the Lipschitz rearrangements of Step 4,
`exists_rearrangement_limit`; the hypothesis `0 ≤ f` is not needed for existence). -/
theorem circle_symmDecrRearr_exists_unique {f : Legacy.TorusEndpoint.Torus 1 → ℝ}
    (hf : Integrable f (Legacy.TorusEndpoint.torusMeasure 1))
    (_hf0 : ∀ᵐ x ∂Legacy.TorusEndpoint.torusMeasure 1, 0 ≤ f x) :
    (∃ F, Obstruction.IsSymmDecrRearr f F) ∧
      ∀ F G, Obstruction.IsSymmDecrRearr f F → Obstruction.IsSymmDecrRearr f G →
        F =ᵐ[Legacy.TorusEndpoint.torusMeasure 1] G :=
  ⟨(PolarizationL1.exists_rearrangement_limit hf).elim fun F hF => ⟨F, hF.identDistrib hf, hF.radial⟩,
    fun _ _ hF hG => hF.ae_unique hG⟩

/-- **`eq:circle-rearr-lipschitz`** (row S011, Step 4 of the printed proof): for Lipschitz `f, g` on the
circle there are continuous `F, G`, equimeasurable with `f, g` and even and nonincreasing in the
geodesic distance everywhere (`eq:circle-rearr-radial` with `Ω = 𝕋`), such that
`f ≤ g ⇒ F ≤ G`, `∫ |F - G| ≤ ∫ |f - g|` and `∬ f Q g ≤ ∬ F Q G` for `Q(x,y) = q(x - y)`.
The order assertion is `rearrangeLipschitz_mono`, i.e. polarization monotonicity (`polarize_mono`,
`PairOrbit.mono`, `pair_closure_mono`). -/
theorem eq_circle_rearr_lipschitz (q : UnitAddCircle → ℝ) {C : ℝ} (hq0 : ∀ z, 0 ≤ q z)
    (hqC : ∀ z, q z ≤ C) (hq : ∀ x y, ‖x‖ ≤ ‖y‖ → q y ≤ q x)
    (f g : Legacy.TorusEndpoint.Torus 1 → ℝ) {K L : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    ∃ F G : Legacy.TorusEndpoint.Torus 1 →ᵇ ℝ,
      IdentDistrib F f (Legacy.TorusEndpoint.torusMeasure 1) (Legacy.TorusEndpoint.torusMeasure 1) ∧
      IdentDistrib G g (Legacy.TorusEndpoint.torusMeasure 1) (Legacy.TorusEndpoint.torusMeasure 1) ∧
      (∀ x y : Legacy.TorusEndpoint.Torus 1, ‖x 0‖ ≤ ‖y 0‖ → F y ≤ F x) ∧
      (∀ x y : Legacy.TorusEndpoint.Torus 1, ‖x 0‖ ≤ ‖y 0‖ → G y ≤ G x) ∧
      ((∀ x, f x ≤ g x) → ∀ x, F x ≤ G x) ∧
      (∫ x, |F x - G x| ∂Legacy.TorusEndpoint.torusMeasure 1) ≤ ∫ x, |f x - g x| ∂Legacy.TorusEndpoint.torusMeasure 1 ∧
      (∫ p : Legacy.TorusEndpoint.Torus 1 × Legacy.TorusEndpoint.Torus 1, f p.1 * q (p.1 0 - p.2 0) * g p.2
          ∂(Legacy.TorusEndpoint.torusMeasure 1).prod (Legacy.TorusEndpoint.torusMeasure 1)) ≤
        (∫ p : Legacy.TorusEndpoint.Torus 1 × Legacy.TorusEndpoint.Torus 1, F p.1 * q (p.1 0 - p.2 0) * G p.2
          ∂(Legacy.TorusEndpoint.torusMeasure 1).prod (Legacy.TorusEndpoint.torusMeasure 1)) := by
  have hC : ∀ z, ‖q z‖ ≤ C := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hq0 z)] using hqC z
  have hm : Measurable q := PolarizationL1.circle_radial_kernel_measurable hq
  have e : ∀ u v : Legacy.TorusEndpoint.Torus 1 → ℝ,
      BilinearPolarization.pairing (fun x y : Legacy.TorusEndpoint.Torus 1 => q (x 0 - y 0)) u v =
        ∫ p : Legacy.TorusEndpoint.Torus 1 × Legacy.TorusEndpoint.Torus 1, u p.1 * q (p.1 0 - p.2 0) * v p.2
          ∂(Legacy.TorusEndpoint.torusMeasure 1).prod (Legacy.TorusEndpoint.torusMeasure 1) := by
    intro u v
    unfold BilinearPolarization.pairing BilinearPolarization.pairingIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  refine ⟨PolarizationL1.rearrangeLipschitz f hf, PolarizationL1.rearrangeLipschitz g hg,
    (PolarizationL1.rearrangeLipschitz_spec f hf).2.2.1,
    (PolarizationL1.rearrangeLipschitz_spec g hg).2.2.1,
    PolarizationL1.steiner_antitone_radius (PolarizationL1.rearrangeLipschitz_spec f hf).2.2.2,
    PolarizationL1.steiner_antitone_radius (PolarizationL1.rearrangeLipschitz_spec g hg).2.2.2,
    fun h x => PolarizationL1.rearrangeLipschitz_mono f g hf hg h x, ?_, ?_⟩
  · simpa only [Real.norm_eq_abs] using PolarizationL1.rearrangeLipschitz_l1_contraction f g hf hg
  · rw [← e, ← e]
    exact PolarizationL1.rearrangeLipschitz_circle_pairing q hm hC hq f g hf hg

/-! ## Row U01: `eq:section2-relative-entropy` -/

/-- **`eq:section2-relative-entropy`** (row U01), every clause of the printed convention, for a
probability measure `μ` and nonnegative `f ∈ L¹(μ)` of mass `m`: the integral of the negative part of
`f log f` is finite; zero mass gives entropy zero; the value is `+∞` exactly when the positive part is
not integrable; when `f log f` is integrable the entropy is `∫ f log f - m log m`, which is
nonnegative (Jensen); and for unit mass it is `∫ f log f`. -/
theorem eq_section2_relative_entropy_printed {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : FiniteMassDomain μ f) :
    (∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x))) ∂μ < ⊤) ∧
    (∫ x, f x ∂μ = 0 → homEntropy μ f = 0) ∧
    (Integrable (fun x => f x * Real.log (f x)) μ ↔ homEntropy μ f ≠ ⊤) ∧
    (Integrable (fun x => f x * Real.log (f x)) μ →
      0 ≤ (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ) ∧
      homEntropy μ f = ENNReal.ofReal ((∫ x, f x * Real.log (f x) ∂μ) -
        (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ))) ∧
    (∫ x, f x ∂μ = 1 → Integrable (fun x => f x * Real.log (f x)) μ →
      homEntropy μ f = ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂μ)) := by
  refine ⟨hf.lintegral_neg_mul_log_lt_top, fun h => homEntropy_of_mass_zero h,
    integrable_mul_log_iff hf, fun hg => ⟨?_, homEntropy_eq_ofReal hf hg⟩, fun h1 hg => ?_⟩
  · -- Jensen: nonnegativity of `∫ f log f - m log m`
    by_cases hm : ∫ x, f x ∂μ = 0
    · have h0 := hf.ae_eq_zero_of_mass_zero hm
      have : ∫ x, f x * Real.log (f x) ∂μ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [h0] with x hx
        simp [hx]
      rw [this, hm]
      simp
    · have hpos : 0 < ∫ x, f x ∂μ := lt_of_le_of_ne hf.mass_nonneg (Ne.symm hm)
      set m := ∫ y, f y ∂μ with hmdef
      have hk1 : Integrable (fun x => f x * (Real.log m + 1)) μ := hf.integrable.mul_const _
      have hk3 : Integrable (fun x => f x * (Real.log m + 1) - m) μ :=
        hk1.sub (integrable_const m)
      have hk2 : ∫ x, (f x * (Real.log m + 1) - m) ∂μ = m * (Real.log m + 1) - m := by
        rw [integral_sub hk1 (integrable_const m), integral_mul_const, integral_const_prob]
      have hint : ∫ x, entropyIntegrand m (f x) ∂μ =
          ∫ x, (f x * Real.log (f x) - (f x * (Real.log m + 1) - m)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          show entropyIntegrand m (f x) =
            f x * Real.log (f x) - (f x * (Real.log m + 1) - m)
          rw [entropyIntegrand_eq hpos]
          ring)
      have hnn : 0 ≤ ∫ x, entropyIntegrand m (f x) ∂μ :=
        integral_nonneg_of_ae (by
          filter_upwards [hf.nonneg] with x hx
          exact entropyIntegrand_nonneg hpos hx)
      rw [hint, integral_sub hg hk3, hk2] at hnn
      nlinarith
  · have := homEntropy_eq_ofReal hf hg
    rw [h1, Real.log_one, mul_zero, sub_zero] at this
    exact this

/-! ## Row S014: `lem:positive-bernstein` -/

open BecknerOnofri.V2.Reaudit.HeatKernel Legacy.BecknerOnofri.FiniteDifferences in
open BecknerOnofri.HighDim.ClosedCubeTaylor (Cube coefficient monomial) in
open scoped ContDiff in
/-- **`lem:positive-bernstein`** (row S014), complete statement: for `f ∈ C^∞([0,1]^d)` with
`∂^α f ≥ 0` for every multi-index `α`, the coefficients `c_α = ∂^α f(0)/α!` are nonnegative,
`∑ c_α = f(1,…,1)`, `f(y) = ∑ c_α y^α` on the cube, and the series converges uniformly on `[0,1]^d`.
Proof as printed (radial absolute monotonicity, monotone convergence, Weierstrass M-test). -/
theorem lem_positive_bernstein_printed {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegMultiIndexPartials f) :
    (∀ a, 0 ≤ coefficient f a) ∧ HasSum (coefficient f) (f 1) ∧
    (∀ y : Cube d, HasSum (fun a => coefficient f a * monomial a y)
      (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, coefficient f a * monomial a y)
      (fun y => f (fun i => (y i : ℝ))) Filter.atTop :=
  positive_bernstein_multiindex hf hpos

open BecknerOnofri.V2.Reaudit.HeatKernel Legacy.BecknerOnofri.FiniteDifferences in
open BecknerOnofri.HighDim.ClosedCubeTaylor (Cube coefficient monomial) in
open scoped ContDiff in
/-- The same statement through the older tensor-Bernstein route
(`ClosedCubeTaylor.closed_cube_expansion`, uniform convergence by `positiveTaylor_uniform`);
the manuscript proof is the radial route of `lem_positive_bernstein_printed`. -/
theorem lem_positive_bernstein_tensor_route {d : ℕ} {f : Space d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedCube d)) (hpos : NonnegMultiIndexPartials f) :
    (∀ a, 0 ≤ coefficient f a) ∧ HasSum (coefficient f) (f 1) ∧
    (∀ y : Cube d, HasSum (fun a => coefficient f a * monomial a y)
      (f (fun i => (y i : ℝ)))) ∧
    TendstoUniformly (fun s : Finset (Index d) => fun y : Cube d =>
      ∑ a ∈ s, coefficient f a * monomial a y)
      (fun y => f (fun i => (y i : ℝ))) Filter.atTop :=
  BecknerOnofri.HighDim.ClosedCubeTaylor.closed_cube_expansion f hf
    ((nonnegativePartials_iff hf).mpr hpos)

/-! ## Row S037: `prop:spectral-marginal-energy` -/

/-- **`prop:spectral-marginal-energy`** (row S037), both displays: for a countable cosine-power mixture
`ρ` in dimension `d ≥ 12`, the deletion form `eq:spectral-energy-main` and, for `d ≥ r ≥ 12`, the
subset form `eq:spectral-energy-r`. -/
theorem prop_spectral_marginal_energy_printed :
    (∀ {d : ℕ}, 12 ≤ d → ∀ ρ : HighDim.ProbabilityDensity d, HighDim.IsCountableCosineMixture ρ →
      HighDim.spectralEnergy ρ ≤ ENNReal.ofReal (1 / ((d : ℝ) - 1)) *
        ∑ i : Fin d, HighDim.inversePowerEnergy (d - 1)
          (HighDim.coordinateMarginal ρ (Finset.univ.erase i))) ∧
    (∀ {d r : ℕ}, 12 ≤ r → r ≤ d → ∀ ρ : HighDim.ProbabilityDensity d,
      HighDim.IsCountableCosineMixture ρ →
      HighDim.spectralEnergy ρ ≤ ENNReal.ofReal ((d : ℝ) / ((r : ℝ) * (d.choose r : ℝ))) *
        ∑ I ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
          HighDim.inversePowerEnergy r (HighDim.coordinateMarginal ρ I)) :=
  ⟨fun hd ρ hρ => Reaudit.Mixtures.spectral_marginal_energy_deletion_direct hd ρ hρ,
    fun hr hrd ρ hρ => Reaudit.Mixtures.spectral_marginal_energy_subset_direct hr hrd ρ hρ⟩

/-! ## Row S040: `cor:section5-high-endpoint` -/

/-- **`cor:section5-high-endpoint`** (row S040) as printed: for `d ≥ 12`, the density inequality
`Ent(ρ) ≥ (2π)^d/2 ‖ρ‖²` with equality only for `ρ = 1`; the dual potential inequality with
coefficient `A_s(d)` and equality only for constants; and `β_gm(d) = β_s(d)`.  The threshold identity
follows the printed proof: `β_s ∈ {P_d = 0}` from the density inequality, and `P_d(β) > 0` for
`β > β_s` from the first-shell obstruction of `lem:section2-universal-obstructions`. -/
theorem cor_section5_high_endpoint_printed (d : ℕ) (hd : 12 ≤ d) :
    (∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) ∧
        (spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) ↔
          ρ.value =ᵐ[torusMeasure d] fun _ => 1)) ∧
    (∀ u : Torus d → ℝ, InCriticalSobolev u →
      Integrable (fun x => Real.exp (centered u x)) (torusMeasure d) ∧
        logPartition u ≤ ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ∧
        (logPartition u = ((spectralCoefficient d * potentialEnergy u : ℝ) : EReal) ↔
          ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => c)) ∧
    VariationalCurves.globalTransition d = spectralThreshold d := by
  have hd0 : 0 < d := by omega
  have hdens := SpinChannel.spectral_high_density_written V2.Final.Unconditional.scalarBounds hd
  have hE : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ ≤ ENNReal.ofReal (2 * entropy ρ) := fun ρ hρ => (hdens ρ hρ).1
  have hR : ∀ ρ : ProbabilityDensity d, ρ.FiniteEntropy →
      spectralEnergy ρ = ENNReal.ofReal (2 * entropy ρ) → ρ.value =ᵐ[torusMeasure d] fun _ => 1 :=
    fun ρ hρ h => ((hdens ρ hρ).2).mp h
  -- `β_s` has zero pressure: dual form of the density inequality
  have hσ := spectralThreshold_pos hd0
  have hmem : pressure d (spectralThreshold d) = 0 := by
    rw [pressure_eq_coefficientDefect hd0 hσ]
    have he : spectralThreshold d / (2 * spectralThreshold d * (2 * Real.pi) ^ d) =
        spectralCoefficient d := by
      unfold spectralCoefficient
      field_simp
    rw [he]
    exact coefficientDefect_spectral_zero_of_primal hd0
      (fun u hu => (potential_endpoint_of_density hd0 hE u hu).2)
  refine ⟨fun ρ hρ => hdens ρ hρ, fun u hu => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨hi, hle⟩ := potential_endpoint_of_density hd0 hE u hu
    exact ⟨hi, hle, potential_rigidity_of_density hd0 hE hR u hu⟩
  · -- every `β` with zero pressure is at most `β_s`: first-shell obstruction
    have hobs := (Obstruction.universal_obstructions hd0).2.2.2.1
    have hmemS : spectralThreshold d ∈ {β : ℝ | 0 ≤ β ∧ pressure d β = 0} := ⟨hσ.le, hmem⟩
    refine csSup_le ⟨_, hmemS⟩ fun β hβ => ?_
    by_contra hlt
    have hpos := hobs β (lt_of_not_ge hlt)
    rw [hβ.2] at hpos
    exact lt_irrefl _ hpos
  · have hobs := (Obstruction.universal_obstructions hd0).2.2.2.1
    have hmemS : spectralThreshold d ∈ {β : ℝ | 0 ≤ β ∧ pressure d β = 0} := ⟨hσ.le, hmem⟩
    refine le_csSup ⟨spectralThreshold d, fun β hβ => ?_⟩ hmemS
    by_contra hlt
    have hpos := hobs β (lt_of_not_ge hlt)
    rw [hβ.2] at hpos
    exact lt_irrefl _ hpos

/-! ## Row S044: the function `ψ` of `prop:section5-spin-entropy` -/

/-- **`prop:section5-spin-entropy`**, the opening assertion: `ψ(t) = t⁴/(14 - 10t²)` is nonnegative,
increasing and convex on `[0, 1]`. -/
theorem prop_section5_psi_properties :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ V2.Circle.psi t) ∧
    MonotoneOn V2.Circle.psi (Set.Icc 0 1) ∧
    ConvexOn ℝ (Set.Icc 0 1) V2.Circle.psi :=
  ⟨fun _ h0 h1 => V2.Circle.psi_nonneg h0 h1,
    fun _ ha _ hb hab => V2.Assembly.psiV2_mono ha.1 hab hb.2,
    V2.Circle.psi_convexOn⟩

#print axioms prop_section2_basic_curve_geometry
#print axioms lem_circle_rearrangement_printed_full
#print axioms eq_circle_rearr_lipschitz
#print axioms eq_section2_relative_entropy_printed
#print axioms lem_positive_bernstein_printed
#print axioms lem_positive_bernstein_tensor_route
#print axioms prop_spectral_marginal_energy_printed
#print axioms cor_section5_high_endpoint_printed
#print axioms prop_section5_psi_properties

end V2.Reaudit.Final
end BecknerOnofri

end
