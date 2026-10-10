module

public import BecknerOnofri.V2.Reaudit.Attainment.Adams
public import BecknerOnofri.V2.Reaudit.Attainment.Basic
public import BecknerOnofri.HeatL1Convergence
public import BecknerOnofri.FiniteEntropyEnergy
public import Legacy.BecknerOnofri.SobolevDensityPairing
public import Legacy.TorusEndpoint.EntropyVariational

@[expose] public section

/-! # Identification of the ordinary integral with the Fourier pairing (package `Attainment`)

Decisions §5.7 (original TeX line 770): for a finite-entropy density `ρ` and `u ∈ H^{d/2}` of mean
zero, `∫ u ρ` is an absolutely convergent integral and equals the Fourier pairing
`∑_{k ≠ 0} û(k) conj(ρ̂(k))`.  Printed route: heat approximation `ρ_t = e^{tΔ}ρ`, uniform integrability
of `u` against `ρ_t` from the Donsker–Varadhan inequality and the exponential integrability of `u`,
and passage to the limit. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate

namespace BecknerOnofri.V2.Reaudit.Attainment
open BecknerOnofri.HighDim

variable {d : ℕ}

/-- `e^{s|u|}` is integrable for a mean-zero `u ∈ H^{d/2}` and every real `s`
(exponential integrability applied to `±s u`). -/
theorem integrable_exp_mul_abs (hd : 0 < d) {u : Torus d → ℝ} (hu : InCriticalSobolev u)
    (hm : MeanZero u) (s : ℝ) :
    Integrable (fun x => Real.exp (s * |u x|)) (torusMeasure d) := by
  obtain ⟨B, hB⟩ := criticalAdamsAboveThreshold_unconditional hd (collapseCoefficient d + 1)
    (by linarith)
  have h1 := (hB (fun x => s * u x) (inCriticalSobolev_const_mul s hu) (meanZero_const_mul s hm)).1
  have h2 := (hB (fun x => (-s) * u x) (inCriticalSobolev_const_mul (-s) hu)
    (meanZero_const_mul (-s) hm)).1
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (s * |u x|)) (torusMeasure d) :=
    (Real.continuous_exp.comp_aestronglyMeasurable
      ((hu.1.aestronglyMeasurable.norm.const_mul s).congr
        (Filter.Eventually.of_forall fun x => by simp)))
  refine (h1.add h2).mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply]
  have e1 := Real.exp_pos (s * u x)
  have e2 := Real.exp_pos ((-s) * u x)
  rcases abs_cases (u x) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    linarith
  · rw [h, show s * -u x = (-s) * u x by ring]
    linarith


/-! ## Products with a density of finite entropy -/

/-- The part of `u` where `|u| > m`, in absolute value: `|u| 1_{|u| > m}`. -/
def tailPart (u : Torus d → ℝ) (m : ℝ) (x : Torus d) : ℝ := if m < |u x| then |u x| else 0

/-- The part of `u` where `|u| ≤ m`: `u 1_{|u| ≤ m}`. -/
def headPart (u : Torus d → ℝ) (m : ℝ) (x : Torus d) : ℝ := if |u x| ≤ m then u x else 0

theorem tailPart_nonneg (u : Torus d → ℝ) (m : ℝ) (x : Torus d) : 0 ≤ tailPart u m x := by
  unfold tailPart; split_ifs <;> simp

theorem tailPart_le (u : Torus d → ℝ) (m : ℝ) (x : Torus d) : tailPart u m x ≤ |u x| := by
  unfold tailPart; split_ifs <;> simp

theorem abs_headPart_le (u : Torus d → ℝ) {m : ℝ} (hm : 0 ≤ m) (x : Torus d) :
    |headPart u m x| ≤ m := by
  unfold headPart; split_ifs with h
  · exact h
  · simpa using hm

theorem abs_sub_headPart (u : Torus d → ℝ) (m : ℝ) (x : Torus d) :
    |u x - headPart u m x| = tailPart u m x := by
  unfold headPart tailPart
  by_cases h : |u x| ≤ m
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]

theorem measurable_headPart {u : Torus d → ℝ} (hu : Measurable u) (m : ℝ) :
    Measurable (headPart u m) := by
  unfold headPart
  exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hu) measurable_const) hu measurable_const

theorem measurable_tailPart {u : Torus d → ℝ} (hu : Measurable u) (m : ℝ) :
    Measurable (tailPart u m) := by
  unfold tailPart
  exact Measurable.ite (measurableSet_lt measurable_const (continuous_abs.measurable.comp hu)) (continuous_abs.measurable.comp hu) measurable_const


section DonskerVaradhan

variable {σ u : Torus d → ℝ}

theorem integrable_mul_abs (hσ0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ σ x)
    (hσi : Integrable σ (torusMeasure d))
    (hσe : Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d))
    (hu : Measurable u) (hexp : Integrable (fun x => Real.exp (1 * |u x|)) (torusMeasure d)) :
    Integrable (fun x => σ x * |u x|) (torusMeasure d) := by
  have hb : Integrable (fun x => σ x * Real.log (σ x) - σ x + Real.exp (1 * |u x|))
      (torusMeasure d) := (hσe.sub hσi).add hexp
  refine hb.mono' (hσi.aestronglyMeasurable.mul
    (continuous_abs.measurable.comp hu).aestronglyMeasurable) ?_
  filter_upwards [hσ0] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (abs_nonneg _))]
  have := Legacy.TorusEndpoint.entropy_young (σ x) |u x| hx
  rw [one_mul]
  linarith

theorem integrable_mul (hσ0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ σ x)
    (hσi : Integrable σ (torusMeasure d))
    (hσe : Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d))
    (hu : Measurable u) (hexp : Integrable (fun x => Real.exp (1 * |u x|)) (torusMeasure d)) :
    Integrable (fun x => σ x * u x) (torusMeasure d) := by
  refine (integrable_mul_abs hσ0 hσi hσe hu hexp).mono'
    (hσi.aestronglyMeasurable.mul hu.aestronglyMeasurable) ?_
  filter_upwards [hσ0] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]

/-- The Donsker–Varadhan inequality applied to `s |u| 1_{|u| > m}`, `s > 0`. -/
theorem tail_bound (hσ0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ σ x)
    (hσi : Integrable σ (torusMeasure d)) (hσm : (∫ x, σ x ∂torusMeasure d) = 1)
    (hσe : Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d))
    (hu : Measurable u) (hexp : ∀ s : ℝ, Integrable (fun x => Real.exp (s * |u x|)) (torusMeasure d))
    (m : ℝ) {s : ℝ} (hs : 0 < s) :
    s * ∫ x, σ x * tailPart u m x ∂torusMeasure d ≤
      (∫ x, σ x * Real.log (σ x) ∂torusMeasure d) +
        Real.log (∫ x, Real.exp (s * tailPart u m x) ∂torusMeasure d) := by
  have hab := integrable_mul_abs hσ0 hσi hσe hu (hexp 1)
  have htm : Measurable (tailPart u m) := measurable_tailPart hu m
  have hprod : Integrable (fun x => σ x * (s * tailPart u m x)) (torusMeasure d) := by
    refine (hab.const_mul s).mono' (hσi.aestronglyMeasurable.mul
      (htm.const_mul s).aestronglyMeasurable) ?_
    filter_upwards [hσ0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (mul_nonneg hs.le (tailPart_nonneg u m x)))]
    have := tailPart_le u m x
    nlinarith [mul_nonneg (mul_nonneg hx hs.le) (sub_nonneg.mpr this)]
  have hex : Integrable (fun x => Real.exp (s * tailPart u m x)) (torusMeasure d) := by
    refine (hexp s).mono' (Real.continuous_exp.measurable.comp (htm.const_mul s)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (tailPart_le u m x) hs.le)
  have h := Legacy.TorusEndpoint.entropy_variational_of_integrable (μ := torusMeasure d) hσ0 hσm
    hσi hσe hprod hex
  have h2 : (∫ x, σ x * (s * tailPart u m x) ∂torusMeasure d) =
      s * ∫ x, σ x * tailPart u m x ∂torusMeasure d := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  linarith

/-- The tail exponential moments tend to `1`. -/
theorem tendsto_integral_exp_tail (hu : Measurable u)
    (hexp : ∀ s : ℝ, Integrable (fun x => Real.exp (s * |u x|)) (torusMeasure d)) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun m : ℕ => ∫ x, Real.exp (s * tailPart u m x) ∂torusMeasure d) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence (μ := torusMeasure d)
    (F := fun (m : ℕ) x => Real.exp (s * tailPart u m x)) (f := fun _ => (1 : ℝ))
    (bound := fun x => Real.exp (s * |u x|))
    (fun m => (Real.continuous_exp.measurable.comp
      ((measurable_tailPart hu m).const_mul s)).aestronglyMeasurable)
    (hexp s) (fun m => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (tailPart_le u m x) hs.le))
    (Filter.Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge |u x|
      filter_upwards [eventually_ge_atTop N] with m hm
      have : ¬ ((m : ℝ) < |u x|) := not_lt.mpr (hN.trans (by exact_mod_cast hm))
      simp [tailPart, this])
  simpa using h


/-- `|∫ σ u - ∫ σ u 1_{|u| ≤ m}| ≤ ∫ σ |u| 1_{|u| > m}`. -/
theorem abs_integral_sub_headPart_le (hσ0 : ∀ᵐ x ∂torusMeasure d, 0 ≤ σ x)
    (hσi : Integrable σ (torusMeasure d))
    (hσe : Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d))
    (hu : Measurable u) (hexp : ∀ s : ℝ, Integrable (fun x => Real.exp (s * |u x|)) (torusMeasure d))
    {m : ℝ} (hm : 0 ≤ m) :
    |(∫ x, σ x * u x ∂torusMeasure d) - ∫ x, σ x * headPart u m x ∂torusMeasure d| ≤
      ∫ x, σ x * tailPart u m x ∂torusMeasure d := by
  have hab := integrable_mul_abs hσ0 hσi hσe hu (hexp 1)
  have hsu := integrable_mul hσ0 hσi hσe hu (hexp 1)
  have hhm : Measurable (headPart u m) := measurable_headPart hu m
  have hsh : Integrable (fun x => σ x * headPart u m x) (torusMeasure d) :=
    hσi.mul_bdd hhm.aestronglyMeasurable (c := m) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_headPart_le u hm x)
  have hst : Integrable (fun x => σ x * tailPart u m x) (torusMeasure d) := by
    refine hab.mono' (hσi.aestronglyMeasurable.mul (measurable_tailPart hu m).aestronglyMeasurable)
      ?_
    filter_upwards [hσ0] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (tailPart_nonneg u m x))]
    exact mul_le_mul_of_nonneg_left (tailPart_le u m x) hx
  rw [← integral_sub hsu hsh]
  have := norm_integral_le_of_norm_le hst (f := fun x => σ x * u x - σ x * headPart u m x) (by
    filter_upwards [hσ0] with x hx
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg hx, Real.norm_eq_abs,
      abs_sub_headPart])
  simpa [Real.norm_eq_abs] using this

/-- For a function bounded by `m`, the pairing against two integrable densities differs by at
most `m` times the `L¹` distance of the densities. -/
theorem abs_integral_sub_le_of_bdd {σ τ h : Torus d → ℝ} (hσ : Integrable σ (torusMeasure d))
    (hτ : Integrable τ (torusMeasure d)) (hh : Measurable h) {m : ℝ}
    (hb : ∀ x, |h x| ≤ m) :
    |(∫ x, σ x * h x ∂torusMeasure d) - ∫ x, τ x * h x ∂torusMeasure d| ≤
      m * ∫ x, ‖σ x - τ x‖ ∂torusMeasure d := by
  have h1 : Integrable (fun x => σ x * h x) (torusMeasure d) :=
    hσ.mul_bdd hh.aestronglyMeasurable (c := m) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)
  have h2 : Integrable (fun x => τ x * h x) (torusMeasure d) :=
    hτ.mul_bdd hh.aestronglyMeasurable (c := m) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hb x)
  rw [← integral_sub h1 h2, ← integral_const_mul]
  have := norm_integral_le_of_norm_le ((hσ.sub hτ).norm.const_mul m)
    (f := fun x => σ x * h x - τ x * h x) (Filter.Eventually.of_forall fun x => by
      rw [← sub_mul, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hb x) (norm_nonneg _))
  simpa [Real.norm_eq_abs] using this

end DonskerVaradhan


/-! ## Physical side of the limit: `∫ ρ_t u → ∫ ρ u` -/

open Legacy.BecknerOnofri.HeatDensityApproximation in
/-- Heat approximation: for a finite-entropy density `ρ` and a mean-zero `u ∈ H^{d/2}`, the
integrals `∫ ρ_{t_n} u` converge to `∫ ρ u` when `t_n ↓ 0`.  Uniform integrability of `u`
against `ρ_{t_n}` comes from the Donsker–Varadhan inequality (`tail_bound`), the entropy
contraction `Ent ρ_t ≤ Ent ρ` and exponential integrability of `u`; the bounded part is handled
by `L¹` convergence of `ρ_t` to `ρ`. -/
theorem tendsto_integral_heat (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    {u : Torus d → ℝ} (hum : Measurable u) (hu : InCriticalSobolev u) (hm : MeanZero u)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (heatDensity (Bridge.density ρ) (ht n)).value x * u x
        ∂torusMeasure d) atTop (𝓝 (∫ x, ρ.value x * u x ∂torusMeasure d)) := by
  have hexp := integrable_exp_mul_abs hd hu hm
  set ρ' : Legacy.TorusEndpoint.ProbabilityDensity d := Bridge.density ρ with hρ'
  have hρ'e : ρ'.FiniteEntropy := hρ
  set H : ℝ := |∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d| with hH
  rw [Metric.tendsto_atTop]
  intro ε hε
  set s : ℝ := 3 * (H + 1) / ε with hs
  have hH0 : 0 ≤ H := abs_nonneg _
  have hs0 : 0 < s := by positivity
  have hsε : s * (ε / 3) = H + 1 := by rw [hs]; field_simp
  -- choose the cutoff `m`
  have hI := tendsto_integral_exp_tail (u := u) hum hexp hs0
  have hlog : Tendsto (fun m : ℕ => Real.log (∫ x, Real.exp (s * tailPart u m x) ∂torusMeasure d))
      atTop (𝓝 (Real.log 1)) := hI.log (by norm_num)
  rw [Real.log_one] at hlog
  obtain ⟨m, hm1⟩ := (hlog.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- uniform tail bound for any density `σ` of entropy at most `entropy ρ`
  have key : ∀ σ : Torus d → ℝ, (∀ᵐ x ∂torusMeasure d, 0 ≤ σ x) → Integrable σ (torusMeasure d) →
      (∫ x, σ x ∂torusMeasure d) = 1 →
      Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d) →
      (∫ x, σ x * Real.log (σ x) ∂torusMeasure d) ≤ ∫ x, ρ.value x * Real.log (ρ.value x)
        ∂torusMeasure d →
      ∫ x, σ x * tailPart u m x ∂torusMeasure d ≤ ε / 3 := by
    intro σ h0 hi hmass he hent
    have h := tail_bound h0 hi hmass he hum hexp m hs0
    have hle : (∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d) ≤ H := le_abs_self _
    have : s * ∫ x, σ x * tailPart u m x ∂torusMeasure d ≤ s * (ε / 3) := by
      rw [hsε]; linarith
    exact le_of_mul_le_mul_left this hs0
  have hρtail := key ρ.value ρ.nonneg ρ.integrable ρ.mass hρ le_rfl
  -- `L¹` convergence of the heat densities controls the bounded part
  have hl1 := BecknerOnofri.HighDim.HeatApproximation.heat_l1_tendsto ρ' t ht ht0
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl1 (ε / (3 * (m + 1))) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  set σ : Torus d → ℝ := (heatDensity ρ' (ht n)).value with hσ
  have hσe : Integrable (fun x => σ x * Real.log (σ x)) (torusMeasure d) :=
    heatDensity_finiteEntropy ρ' (ht n)
  have hσtail := key σ (heatDensity ρ' (ht n)).nonneg (heatDensity ρ' (ht n)).integrable
    (heatDensity ρ' (ht n)).mass hσe (heatDensity_entropy_le ρ' hρ'e (ht n))
  have e1 := abs_integral_sub_headPart_le (σ := σ) (u := u) (heatDensity ρ' (ht n)).nonneg
    (heatDensity ρ' (ht n)).integrable hσe hum hexp hm0
  have e2 := abs_integral_sub_headPart_le (σ := ρ.value) (u := u) ρ.nonneg ρ.integrable hρ hum hexp
    hm0
  have e3 := abs_integral_sub_le_of_bdd (σ := σ) (τ := ρ.value) (h := headPart u m)
    (heatDensity ρ' (ht n)).integrable ρ.integrable (measurable_headPart hum m)
    (fun x => abs_headPart_le u hm0 x)
  have hd1 := hN n hn
  rw [Real.dist_eq, sub_zero] at hd1
  have hl1n : ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d < ε / (3 * (m + 1)) := by
    have : BecknerOnofri.HighDim.HeatApproximation.l1distance (heatValue ρ' (t n)) ρ.value =
        ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d := rfl
    rw [← this]
    exact lt_of_le_of_lt (le_abs_self _) hd1
  have hmε : (m : ℝ) * ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d < ε / 3 := by
    have h1 : (m : ℝ) * ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d ≤
        ((m : ℝ) + 1) * ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d :=
      mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg fun x => norm_nonneg _)
    have h2 : ((m : ℝ) + 1) * ∫ x, ‖σ x - ρ.value x‖ ∂torusMeasure d <
        ((m : ℝ) + 1) * (ε / (3 * (m + 1))) :=
      mul_lt_mul_of_pos_left hl1n (by positivity)
    have h3 : ((m : ℝ) + 1) * (ε / (3 * (m + 1))) = ε / 3 := by field_simp
    linarith
  rw [Real.dist_eq]
  set a1 := ∫ x, σ x * u x ∂torusMeasure d
  set a2 := ∫ x, σ x * headPart u m x ∂torusMeasure d
  set b1 := ∫ x, ρ.value x * u x ∂torusMeasure d
  set b2 := ∫ x, ρ.value x * headPart u m x ∂torusMeasure d
  have : |a1 - b1| ≤ |a1 - a2| + |a2 - b2| + |b2 - b1| := by
    calc |a1 - b1| = |(a1 - a2) + (a2 - b2) + (b2 - b1)| := by ring_nf
      _ ≤ _ := abs_add_three _ _ _
  rw [abs_sub_comm b2 b1] at this
  linarith


/-! ## Fourier side of the limit -/

/-- Weighted arithmetic-geometric mean inequality: `x y ≤ (w x² + y²/w)/2` for `w > 0`. -/
theorem mul_le_half_weighted {x y w : ℝ} (hw : 0 < w) :
    x * y ≤ (w * x ^ 2 + y ^ 2 / w) / 2 := by
  have h := div_nonneg (sq_nonneg (w * x - y)) hw.le
  have h2 : (w * x - y) ^ 2 / w = w * x ^ 2 - 2 * (x * y) + y ^ 2 / w := by
    field_simp
    ring
  linarith

/-- The series `∑_k |û(k)| |ρ̂(k)|` converges for `u ∈ H^{d/2}` of mean zero and a density of finite
entropy (Cauchy–Schwarz against the finiteness of `∑_{k≠0} |k|^{-d} |ρ̂(k)|²`). -/
theorem summable_norm_pairing (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    Summable (fun k : Frequency d => ‖fourierCoeff u k‖ * ‖fourierCoeff ρ.value k‖) := by
  set f : Frequency d → ℝ := fun k => ‖fourierCoeff u k‖ * ‖fourierCoeff ρ.value k‖ with hf
  have hsupp : Function.support f ⊆ {k : Frequency d | k ≠ 0} := by
    intro k hk hk0
    subst hk0
    apply hk
    show ‖fourierCoeff u 0‖ * ‖fourierCoeff ρ.value 0‖ = 0
    rw [BecknerOnofri.V2.Onset.fourierCoeff_zero_meanZero hm, norm_zero, zero_mul]
  have hc : 0 < (2 * Real.pi) ^ d := pow_pos (by positivity) d
  have hs : Summable (fun k : NonzeroFrequency d => f k.val) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (((hu.2.mul_right ((2 * Real.pi) ^ d)⁻¹).add
        (finiteEntropy_spectralTerm_summable hd ρ hρ)).mul_left (1 / 2))
    have hL : 0 < frequencyLength k.val ^ d :=
      pow_pos (lt_of_lt_of_le zero_lt_one (BecknerOnofri.V2.Onset.one_le_frequencyLength k.2)) d
    have h := mul_le_half_weighted (x := ‖fourierCoeff u k.val‖) (y := ‖fourierCoeff ρ.value k.val‖)
      hL
    have e1 : potentialTerm u k * ((2 * Real.pi) ^ d)⁻¹ =
        frequencyLength k.val ^ d * ‖fourierCoeff u k.val‖ ^ 2 := by
      unfold potentialTerm
      rw [mul_pow]
      field_simp
    have e2 : spectralTerm ρ k = ‖fourierCoeff ρ.value k.val‖ ^ 2 / frequencyLength k.val ^ d := by
      unfold spectralTerm
      rw [inv_mul_eq_div]
    show ‖fourierCoeff u k.val‖ * ‖fourierCoeff ρ.value k.val‖ ≤
      1 / 2 * (potentialTerm u k * ((2 * Real.pi) ^ d)⁻¹ + spectralTerm ρ k)
    rw [e1, e2]
    linarith
  exact (hasSum_subtype_iff_of_support_subset hsupp).mp hs.hasSum |>.summable

open Legacy.BecknerOnofri.HeatDensityApproximation in
/-- The Fourier pairing of the heat approximations converges to the Fourier pairing of `ρ`, and the
Fourier pairing of the heat approximation equals the ordinary integral (Parseval, `ρ_t ∈ L²`). -/
theorem pairing_identification_of_measurable (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) {u : Torus d → ℝ} (hum : Measurable u) (hu : InCriticalSobolev u)
    (hm : MeanZero u) :
    Integrable (fun x => ρ.value x * u x) (torusMeasure d) ∧
      HasSum (fun k : Frequency d => (conj (fourierCoeff u k) * fourierCoeff ρ.value k).re)
        (∫ x, ρ.value x * u x ∂torusMeasure d) := by
  have hexp := integrable_exp_mul_abs hd hu hm
  refine ⟨integrable_mul ρ.nonneg ρ.integrable hρ hum (hexp 1), ?_⟩
  set ρ' : Legacy.TorusEndpoint.ProbabilityDensity d := Bridge.density ρ with hρ'
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ht
  have ht0 : ∀ n, 0 < t n := fun n => by positivity
  have htlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → Frequency d → ℝ := fun n k =>
    (conj (fourierCoeff u k) * Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k).re with hF
  set G : Frequency d → ℝ := fun k => (conj (fourierCoeff u k) * fourierCoeff ρ.value k).re with hG
  have hsum := summable_norm_pairing hd ρ hρ hu hm
  -- Parseval for each heat approximation
  have hPars : ∀ n, HasSum (F n) (∫ x, (heatDensity ρ' (ht0 n)).value x * u x ∂torusMeasure d) := by
    intro n
    have hr : MemLp (heatDensity ρ' (ht0 n)).value 2 (torusMeasure d) :=
      (heatValue_continuous ρ' (ht0 n)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := Legacy.BecknerOnofri.SobolevDensityPairing.hasSum_pairing
      (Bridge.potentialLp u hu.1) (heatDensity ρ' (ht0 n)) hr
    have e1 : (fun k : Frequency d =>
        (conj (Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (Bridge.potentialLp u hu.1) k) *
          Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k).re) = F n := by
      funext k
      simp only [hF, Bridge.potentialLp_fourier]
    have e2 : (∫ x, (heatDensity ρ' (ht0 n)).value x * ((Bridge.potentialLp u hu.1) x).re
        ∂torusMeasure d) = ∫ x, (heatDensity ρ' (ht0 n)).value x * u x ∂torusMeasure d := by
      apply integral_congr_ae
      filter_upwards [Bridge.potentialLp_ae u hu.1] with x hx
      rw [hx]
      simp
    rw [e1] at h
    convert h using 1
    exact e2.symm
  -- termwise limit and domination
  have hlim : ∀ k, Tendsto (fun n => F n k) atTop (𝓝 (G k)) := by
    intro k
    have h := heatDensity_fourier_tendsto ρ' t ht0 htlim k
    exact (Complex.continuous_re.tendsto _).comp (tendsto_const_nhds.mul h)
  have hbd : ∀ n k, ‖F n k‖ ≤ ‖fourierCoeff u k‖ * ‖fourierCoeff ρ.value k‖ := by
    intro n k
    have hw : ‖Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k‖ ≤ ‖fourierCoeff ρ.value k‖ := by
      have e : Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k =
          ((Legacy.TorusEndpoint.TorusHeatBounds.heatWeight (t n) k : ℝ) : ℂ) *
            Legacy.TorusEndpoint.densityFourier ρ'.value k := heatValue_fourier ρ' (ht0 n) k
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
        (Legacy.TorusEndpoint.TorusHeatBounds.heatWeight_pos _ _)]
      have h1 := Legacy.TorusEndpoint.GreenHeatRegularization.heatWeight_le_one (ht0 n).le k
      calc _ ≤ 1 * ‖Legacy.TorusEndpoint.densityFourier ρ'.value k‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖fourierCoeff ρ.value k‖ := by rw [one_mul]; rfl
    calc ‖F n k‖ = |(conj (fourierCoeff u k) * Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k).re| :=
          Real.norm_eq_abs _
      _ ≤ ‖conj (fourierCoeff u k) * Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k‖ :=
          Complex.abs_re_le_norm _
      _ = ‖fourierCoeff u k‖ * ‖Legacy.TorusEndpoint.densityFourier (heatDensity ρ' (ht0 n)).value k‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  have hT := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbd)
  have hT' : Tendsto (fun n => ∑' k, F n k) atTop
      (𝓝 (∫ x, ρ.value x * u x ∂torusMeasure d)) := by
    simp_rw [(hPars _).tsum_eq]
    exact tendsto_integral_heat hd ρ hρ hum hu hm t ht0 htlim
  have hGsum : Summable G := Summable.of_norm_bounded hsum (fun k => by
    calc ‖G k‖ = |(conj (fourierCoeff u k) * fourierCoeff ρ.value k).re| := Real.norm_eq_abs _
      _ ≤ ‖conj (fourierCoeff u k) * fourierCoeff ρ.value k‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj])
  have := tendsto_nhds_unique hT hT'
  rw [← this]
  exact hGsum.hasSum

theorem fourierCoeff_congr_ae' {u v : Torus d → ℝ} (h : u =ᵐ[torusMeasure d] v) (k : Frequency d) :
    fourierCoeff u k = fourierCoeff v k := by
  unfold BecknerOnofri.HighDim.fourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- **Identification of the ordinary integral with the Fourier pairing** (decisions §5.7).
For a probability density `ρ` of finite entropy and a mean-zero `u ∈ H^{d/2}`, the function `ρ u` is
integrable and `∫ ρ u = ∑_k Re(conj(û(k)) ρ̂(k))`, the series converging absolutely. -/
theorem pairing_identification (hd : 0 < d) (ρ : ProbabilityDensity d) (hρ : ρ.FiniteEntropy)
    {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    Integrable (fun x => ρ.value x * u x) (torusMeasure d) ∧
      HasSum (fun k : Frequency d => (conj (fourierCoeff u k) * fourierCoeff ρ.value k).re)
        (∫ x, ρ.value x * u x ∂torusMeasure d) := by
  set v : Torus d → ℝ := hu.1.aestronglyMeasurable.mk u with hv
  have huv : u =ᵐ[torusMeasure d] v := hu.1.aestronglyMeasurable.ae_eq_mk
  have hvm : Measurable v := hu.1.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvS : InCriticalSobolev v := by
    refine ⟨hu.1.ae_eq huv, ?_⟩
    have : potentialTerm v = potentialTerm u := by
      funext k
      unfold potentialTerm
      rw [fourierCoeff_congr_ae' huv k.val]
    rw [this]
    exact hu.2
  have hvZ : MeanZero v := by
    unfold MeanZero at *
    rw [← integral_congr_ae huv]
    exact hm
  obtain ⟨h1, h2⟩ := pairing_identification_of_measurable hd ρ hρ hvm hvS hvZ
  have hce : (fun x => ρ.value x * u x) =ᵐ[torusMeasure d] fun x => ρ.value x * v x := by
    filter_upwards [huv] with x hx
    rw [hx]
  refine ⟨h1.congr hce.symm, ?_⟩
  have e : (∫ x, ρ.value x * v x ∂torusMeasure d) = ∫ x, ρ.value x * u x ∂torusMeasure d :=
    (integral_congr_ae hce).symm
  rw [e] at h2
  simpa only [fourierCoeff_congr_ae' huv] using h2

/-- The same identity with the sum over `k ≠ 0` (the term `k = 0` vanishes since `û(0) = 0`):
`∫ ρ u = ∑_{k ≠ 0} Re(conj(û(k)) ρ̂(k))`. -/
theorem pairing_identification_nonzero (hd : 0 < d) (ρ : ProbabilityDensity d)
    (hρ : ρ.FiniteEntropy) {u : Torus d → ℝ} (hu : InCriticalSobolev u) (hm : MeanZero u) :
    HasSum
      (fun k : NonzeroFrequency d => (conj (fourierCoeff u k.val) * fourierCoeff ρ.value k.val).re)
      (∫ x, ρ.value x * u x ∂torusMeasure d) := by
  have h := (pairing_identification hd ρ hρ hu hm).2
  have hsupp : Function.support
      (fun k : Frequency d => (conj (fourierCoeff u k) * fourierCoeff ρ.value k).re) ⊆
        {k : Frequency d | k ≠ 0} := by
    intro k hk hk0
    subst hk0
    apply hk
    show (conj (fourierCoeff u 0) * fourierCoeff ρ.value 0).re = 0
    rw [BecknerOnofri.V2.Onset.fourierCoeff_zero_meanZero hm]
    simp
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr h

end BecknerOnofri.V2.Reaudit.Attainment
