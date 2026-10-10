module

public import BecknerOnofri.V2.Reaudit.Attainment.Adams
public import BecknerOnofri.V2.Reaudit.Attainment.Rellich
public import BecknerOnofri.V2.Reaudit.Attainment.Vitali

@[expose] public section

/-! # The direct method (`prop:section2-subcritical-attainment`, existence part; row S010)

Printed proof: coercivity from `eq:section2-critical-adams`; a maximizing sequence is bounded in
`H^{d/2}`; weak compactness and Rellich give `u_n → u` in `L²` and almost everywhere
(`eq:section2-maximizer-compactness`); the critical Adams inequality applied to `2u_n` shows
`(e^{u_n})` is bounded in `L²`, hence uniformly integrable, and Vitali's theorem gives
`∫ e^{u_n} → ∫ e^u` (`eq:section2-exponential-vitali`); weak lower semicontinuity of the seminorm
shows that `u` attains `C_d(A)`.

`exists_coefficient_maximizer` follows these steps with `CriticalAdamsAboveThreshold d` as the
form of `eq:section2-critical-adams` that is used; the corollaries instantiate it with the printed
`CriticalAdamsInput d` and with the unconditional rough bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- The real value `log ∫ e^{u-ū} - A ‖u‖²_{Ḣ^{d/2}}` of the functional defining `C_d(A)`. -/
def coefficientValue (A : ℝ) (u : Torus d → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (centered u x) ∂torusMeasure d) - A * potentialEnergy u

theorem inCriticalSobolev_zero : InCriticalSobolev (fun _ : Torus d => (0 : ℝ)) := by
  refine ⟨memLp_const _, ?_⟩
  refine summable_zero.congr fun k => ?_
  have : fourierCoeff (fun _ : Torus d => (0 : ℝ)) k.val = 0 := by
    have h := fourierCoeff_const_mul 0 (fun _ : Torus d => (1 : ℝ)) k.val
    simp only [zero_mul, Complex.ofReal_zero] at h
    exact h
  simp [potentialTerm, this]

theorem coefficientValue_zero (A : ℝ) : coefficientValue A (fun _ : Torus d => (0 : ℝ)) = 0 := by
  have hp : potentialEnergy (fun _ : Torus d => (0 : ℝ)) = 0 := by
    have h := potentialEnergy_const_mul 0 (fun _ : Torus d => (1 : ℝ))
    simpa using h
  unfold coefficientValue
  rw [hp]
  simp [centered]

theorem coefficientValue_centered {u : Torus d → ℝ} (hu : InCriticalSobolev u) (A : ℝ) :
    coefficientValue A (centered u) = coefficientValue A u := by
  unfold coefficientValue
  rw [centered_eq_self (meanZero_centered hu.1), potentialEnergy_centered hu.1]

theorem logPartition_sub_eq_coefficientValue (hd : 0 < d) (A : ℝ) {u : Torus d → ℝ}
    (hu : InCriticalSobolev u) :
    logPartition u - ((A * potentialEnergy u : ℝ) : EReal) = (coefficientValue A u : EReal) := by
  rw [logPartition_eq_log_integral hd u hu, ← EReal.coe_sub]
  rfl

/-- Coercivity (`eq:section2-subcritical-coercivity`): for `a > A_crit`,
`C-value(u) ≤ B - (A - a) ‖u‖²`. -/
theorem coercivity {A a B : ℝ}
    (hB : ∀ u : Torus d → ℝ, InCriticalSobolev u → MeanZero u →
      Integrable (fun x => Real.exp (u x)) (torusMeasure d) ∧
        Real.log (∫ x, Real.exp (u x) ∂torusMeasure d) ≤ a * potentialEnergy u + B)
    {v : Torus d → ℝ} (hv : InCriticalSobolev v) :
    coefficientValue A v ≤ B - (A - a) * potentialEnergy v := by
  have h := (hB (centered v) (inCriticalSobolev_centered hv) (meanZero_centered hv.1)).2
  rw [potentialEnergy_centered hv.1] at h
  unfold coefficientValue
  linarith


/-- **Existence of a maximizer for `C_d(A)`** (`prop:section2-subcritical-attainment`, first
assertion), following the printed proof.  `A` is any coefficient above `A_crit(d)`; the maximizer is
a mean-zero `u ∈ H^{d/2}` for the functional `log ∫ e^{u-ū} - A ‖u‖²_{Ḣ^{d/2}}`. -/
theorem exists_coefficient_maximizer (hd : 0 < d) (hAd : CriticalAdamsAboveThreshold d) {A : ℝ}
    (hA : collapseCoefficient d < A) :
    ∃ u : Torus d → ℝ, InCriticalSobolev u ∧ MeanZero u ∧
      ∀ v : Torus d → ℝ, InCriticalSobolev v → coefficientValue A v ≤ coefficientValue A u := by
  have hc0 : 0 < collapseCoefficient d := by
    unfold collapseCoefficient
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have := Legacy.TorusEndpoint.endpointSigma_pos hd
    positivity
  set a : ℝ := (A + collapseCoefficient d) / 2 with ha
  have ha1 : collapseCoefficient d < a := by rw [ha]; linarith
  have ha2 : a < A := by rw [ha]; linarith
  have ha0 : 0 < a := lt_trans hc0 ha1
  obtain ⟨B, hB⟩ := hAd a ha1
  have hAa : 0 < A - a := sub_pos.mpr ha2
  -- the supremum
  set R : Set ℝ := Set.range (fun v : {v : Torus d → ℝ // InCriticalSobolev v} =>
    coefficientValue A v.1) with hR
  have hne : R.Nonempty := ⟨coefficientValue A (fun _ : Torus d => (0 : ℝ)),
    ⟨⟨_, inCriticalSobolev_zero⟩, rfl⟩⟩
  have hbdd : BddAbove R := by
    refine ⟨B, ?_⟩
    rintro _ ⟨v, rfl⟩
    have := coercivity (A := A) hB v.2
    have hE : 0 ≤ potentialEnergy v.1 := potentialEnergy_nonneg _
    nlinarith
  set S : ℝ := sSup R with hS
  have hSle : ∀ v : Torus d → ℝ, InCriticalSobolev v → coefficientValue A v ≤ S :=
    fun v hv => le_csSup hbdd ⟨⟨v, hv⟩, rfl⟩
  have hS0 : 0 ≤ S := by
    have := hSle _ (inCriticalSobolev_zero (d := d))
    rwa [coefficientValue_zero] at this
  -- a maximizing sequence of centered potentials
  have hex : ∀ n : ℕ, ∃ v : Torus d → ℝ, InCriticalSobolev v ∧
      S - 1 / ((n : ℝ) + 1) < coefficientValue A v := by
    intro n
    obtain ⟨_, ⟨v, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne
      (sub_lt_self S (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    exact ⟨v.1, v.2, hv⟩
  choose w hw hwv using hex
  set u : ℕ → Torus d → ℝ := fun n => centered (w n) with hu
  have huc : ∀ n, InCriticalSobolev (u n) := fun n => inCriticalSobolev_centered (hw n)
  have hum : ∀ n, MeanZero (u n) := fun n => meanZero_centered (hw n).1
  have huv : ∀ n : ℕ, S - 1 / ((n : ℝ) + 1) < coefficientValue A (u n) := fun n => by
    rw [hu]; dsimp only; rw [coefficientValue_centered (hw n)]; exact hwv n
  have huS : ∀ n : ℕ, coefficientValue A (u n) ≤ S := fun n => hSle _ (huc n)
  -- energy bound
  set E₀ : ℝ := (B + 1) / (A - a) with hE₀
  have hE : ∀ n : ℕ, potentialEnergy (u n) ≤ E₀ := by
    intro n
    have h1 := coercivity (A := A) hB (huc n)
    have h2 := huv n
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [hE₀, le_div_iff₀ hAa]
    nlinarith
  obtain ⟨φ, v, hφ, hvc, hvm, hL2, hae, hlsc⟩ := exists_L2_ae_limit hd u huc hum hE
  -- `(e^{u_n})` is bounded in `L²`: apply the Adams bound to `2 u_n`
  have h2 : ∀ n : ℕ, Integrable (fun x => Real.exp (2 * u n x)) (torusMeasure d) ∧
      ∫ x, Real.exp (2 * u n x) ∂torusMeasure d ≤ Real.exp (4 * a * E₀ + B) := by
    intro n
    obtain ⟨hint, hlog⟩ := hB (fun x => 2 * u n x) (inCriticalSobolev_const_mul 2 (huc n))
      (meanZero_const_mul 2 (hum n))
    refine ⟨hint, ?_⟩
    rw [potentialEnergy_const_mul] at hlog
    calc ∫ x, Real.exp (2 * u n x) ∂torusMeasure d
        = Real.exp (Real.log (∫ x, Real.exp (2 * u n x) ∂torusMeasure d)) :=
          (Real.exp_log (integral_exp_pos hint)).symm
      _ ≤ Real.exp (a * (2 ^ 2 * potentialEnergy (u n)) + B) := Real.exp_le_exp.mpr hlog
      _ ≤ Real.exp (4 * a * E₀ + B) := by
          apply Real.exp_le_exp.mpr
          have := hE n
          nlinarith
  have hsq : ∀ n x, Real.exp (u n x) ^ 2 = Real.exp (2 * u n x) := fun n x => by
    rw [sq, ← Real.exp_add]; ring_nf
  have hvint := (hB v hvc hvm).1
  have hVit : Tendsto (fun n => ∫ x, Real.exp (u (φ n) x) ∂torusMeasure d) atTop
      (𝓝 (∫ x, Real.exp (v x) ∂torusMeasure d)) := by
    refine tendsto_integral_of_ae_of_sq_bound (M := Real.exp (4 * a * E₀ + B))
      (fun n => Real.continuous_exp.comp_aestronglyMeasurable (huc (φ n)).1.aestronglyMeasurable)
      (fun n => by simpa only [hsq] using (h2 (φ n)).1)
      (fun n => by simpa only [hsq] using (h2 (φ n)).2) hvint ?_
    filter_upwards [hae] with x hx
    exact (Real.continuous_exp.tendsto _).comp hx
  have hlogT : Tendsto (fun n => Real.log (∫ x, Real.exp (u (φ n) x) ∂torusMeasure d)) atTop
      (𝓝 (Real.log (∫ x, Real.exp (v x) ∂torusMeasure d))) :=
    hVit.log (integral_exp_pos hvint).ne'
  -- v attains the supremum
  have hvS : S ≤ coefficientValue A v := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hA0 : 0 < A := by linarith
    have hδ : 0 < ε / (3 + A) := by positivity
    have e1 : ∀ᶠ n in atTop, |Real.log (∫ x, Real.exp (u (φ n) x) ∂torusMeasure d) -
        Real.log (∫ x, Real.exp (v x) ∂torusMeasure d)| < ε / (3 + A) :=
      (Metric.tendsto_nhds.mp hlogT) _ hδ
    have e2 := hlsc _ hδ
    have e3 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / (3 + A) := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((3 + A) / ε)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : ((3 + A) / ε) < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      rw [div_lt_iff₀ hε] at hn'
      nlinarith
    have e4 : ∀ᶠ n : ℕ in atTop, 1 / ((φ n : ℝ) + 1) < ε / (3 + A) := by
      have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
      exact hφt.eventually e3
    obtain ⟨n, hn1, hn2, hn3⟩ := (e1.and (e2.and e4)).exists
    have hk := huv (φ n)
    have hcv : coefficientValue A (u (φ n)) =
        Real.log (∫ x, Real.exp (u (φ n) x) ∂torusMeasure d) - A * potentialEnergy (u (φ n)) := by
      unfold coefficientValue
      rw [centered_eq_self (hum (φ n))]
    have hcv' : coefficientValue A v =
        Real.log (∫ x, Real.exp (v x) ∂torusMeasure d) - A * potentialEnergy v := by
      unfold coefficientValue
      rw [centered_eq_self hvm]
    rw [hcv']
    rw [hcv] at hk
    have h1 := (abs_lt.mp hn1).1
    have h2' := (abs_lt.mp hn1).2
    have hAδ : A * potentialEnergy v ≤ A * (potentialEnergy (u (φ n)) + ε / (3 + A)) :=
      mul_le_mul_of_nonneg_left hn2 hA0.le
    have hε3 : (3 + A) * (ε / (3 + A)) = ε := by field_simp
    nlinarith
  refine ⟨v, hvc, hvm, fun w hw => ?_⟩
  exact (hSle w hw).trans hvS

end BecknerOnofri.V2.Reaudit.Attainment
