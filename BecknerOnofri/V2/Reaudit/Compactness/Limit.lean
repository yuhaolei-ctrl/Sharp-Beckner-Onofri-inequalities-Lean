module

public import BecknerOnofri.SubcriticalOptimizerCompactness
public import BecknerOnofri.V2.Reaudit.Compactness.Vitali
public import BecknerOnofri.V2.Reaudit.Compactness.RadonRiesz

@[expose] public section

/-! # The compactness half of `prop:section4-first-order-coexistence`

Manuscript (Section 4, proof of `prop:section4-first-order-coexistence`, from
`eq:section4-uniform-coercivity-gap` to `eq:section4-strong-critical-Sobolev`).  Let `A_n → A_gm`
with `A_gm > A_s > A_crit`, and let `u_n` maximize the dual functional at `A_n` with values
`C(A_n) → 0` (the pressure limit `eq:section4-pressure-limit-zero`).  The printed steps are:

1. uniform coercivity bounds `(u_n)` in the critical space `H^{d/2}` (`eventual_energy_bound`);
2. weak compactness and Rellich--Kondrachov: a subsequence converges weakly in `H^{d/2}`, strongly in
   `L²`, almost everywhere (`eq:section4-uniform-compactness`; here: `realSobolevBall_isCompact`, then
   a.e. convergence of a further `L²` subsequence);
3. uniform exponential moments for each `p > 1` (`eq:section4-uniform-exponential-p-bound`;
   here: the hypothesis `RoughExponentialBound d b Ab`, which for the callers in `TransitionLimit` is
   *the printed critical Adams inequality applied to `p u`*: `ExternalInputs.roughExponentialBound_of_criticalAdams`
   with `b = endpointConstant d`, `1/(4b) = A_crit(d)` in the energy normalization, and `Ab = exp B_d`;
   `p^2 E/(4b) + log Ab` is the printed bound `B_d + A_crit p^2 ‖u‖^2`);
4. uniform integrability and Vitali: `∫ e^{u_n} → ∫ e^{u_0}` (`eq:section4-vitali-exponential`);
5. weak lower semicontinuity of the quadratic norm and the value convergence show that `u_0` is a
   maximizer at `A_gm` (`eq:section4-limit-is-maximizer`);
6. from the maximizing identity `A_n ‖u_n‖² = log ∫ e^{u_n} - C(A_n)`, the quadratic norms converge
   (`eq:section4-energy-norm-convergence`), and weak convergence plus norm convergence give
   **strong** convergence in `H^{d/2}` (`eq:section4-strong-critical-Sobolev`).

Everything is dimension independent.  Nothing here uses the old endpoint theorems. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace BecknerOnofri.V2.Reaudit.Compactness
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

variable {d : ℕ}

/-! ## Elementary measure-theoretic facts about `L²(𝕋^d, ℂ)` potentials -/

theorem aestronglyMeasurable_exp_re (U : TorusL2 d) (p : ℝ) :
    AEStronglyMeasurable (fun x => Real.exp (p * (U x).re)) (torusMeasure d) :=
  (Real.continuous_exp.comp (continuous_const.mul Complex.continuous_re)).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable U)

theorem exp_re_sq (U : TorusL2 d) (x : Torus d) :
    Real.exp ((U x).re) ^ 2 = Real.exp (2 * (U x).re) := by
  rw [← Real.exp_nat_mul]; norm_num

/-- `L²` convergence has an almost-everywhere convergent subsequence. -/
theorem exists_subseq_tendsto_ae {U : ℕ → TorusL2 d} {V : TorusL2 d} (h : Tendsto U atTop (𝓝 V)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => U (ψ n) x) atTop (𝓝 (V x)) := by
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' U V).1 h
  have h2 : TendstoInMeasure (torusMeasure d) (fun n => ⇑(U n)) atTop ⇑V :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) h1
  exact h2.exists_seq_tendsto_ae

/-- The Fourier coefficients of an `L²`-convergent sequence converge: weak convergence in every
weighted `ℓ²`-space of bounded sequences is coefficientwise convergence. -/
theorem tendsto_coefficient {U : ℕ → TorusL2 d} {V : TorusL2 d} (h : Tendsto U atTop (𝓝 V))
    (k : Frequency d) :
    Tendsto (fun n => fourierIsometry d (U n) k) atTop (𝓝 (fourierIsometry d V k)) :=
  ((lp.lipschitzWith_one_eval 2 k).continuous.tendsto _).comp
    (((fourierIsometry d).continuous.tendsto V).comp h)

/-! ## The functional along a sequence -/

theorem functional_eq (A : ℝ) (U : TorusL2 d) :
    functional A U = Real.log (partition U) - A * criticalEnergy U := rfl

/-- **Compactness half of `prop:section4-first-order-coexistence`.**

Let `U_n` be maximizers of `functional (A_n)` over the admissible potentials, with `A_n → A₀`,
`A₀ > 1/(4b)` (the uniform subcritical gap, `b` the exponent of a rough exponential bound), and the
maximal values `functional (A_n) (U_n) → 0` (the limit of the pressure, `eq:section4-pressure-limit-zero`).
Then along a subsequence `ψ`:

* `U_{ψ n} → U₀` in `L²` and almost everywhere (as real parts), `U₀` in the same critical energy ball;
* the exponential moments `∫ e^{p Re U_{ψ n}}` are bounded uniformly in `n` for every `p > 0`;
* the partition functions converge, `∫ e^{U_{ψ n}} → ∫ e^{U₀}` (Vitali);
* `U₀` is a global maximizer of `functional A₀` with value `0`;
* the critical energies converge, and
* `U_{ψ n} → U₀` **strongly in the critical Sobolev space**: `‖U_{ψ n} - U₀‖²_{Ḣ^{d/2}} → 0`. -/
theorem compactness_limit (hd : 0 < d) {b Ab A₀ : ℝ} (hb : 0 < b)
    (hR : RoughExponentialBound d b Ab) (hgap : 1 / (4 * b) < A₀) {A : ℕ → ℝ}
    (hA : Tendsto A atTop (𝓝 A₀)) (U : ℕ → TorusL2 d) (hU : ∀ n, Admissible (U n))
    (hmax : ∀ n (V : TorusL2 d), Admissible V → functional (A n) V ≤ functional (A n) (U n))
    (hval : Tendsto (fun n => functional (A n) (U n)) atTop (𝓝 0)) :
    ∃ (B : ℝ) (U₀ : TorusL2 d) (ψ : ℕ → ℕ), 0 ≤ B ∧ StrictMono ψ ∧ U₀ ∈ realSobolevBall d B ∧
      (∀ n, U (ψ n) ∈ realSobolevBall d B) ∧
      Tendsto (fun n => U (ψ n)) atTop (𝓝 U₀) ∧
      (∀ᵐ x ∂torusMeasure d, Tendsto (fun n => (U (ψ n) x).re) atTop (𝓝 (U₀ x).re)) ∧
      (∀ p : ℝ, 0 < p → ∀ n, ∫ x, Real.exp (p * (U (ψ n) x).re) ∂torusMeasure d ≤
          Real.exp (p ^ 2 * B / (4 * b) + Real.log Ab)) ∧
      Tendsto (fun n => partition (U (ψ n))) atTop (𝓝 (partition U₀)) ∧
      functional A₀ U₀ = 0 ∧
      (∀ W : TorusL2 d, Admissible W → functional A₀ W ≤ functional A₀ U₀) ∧
      Tendsto (fun n => criticalEnergy (U (ψ n))) atTop (𝓝 (criticalEnergy U₀)) ∧
      Tendsto (fun n => criticalEnergy (U (ψ n) - U₀)) atTop (𝓝 0) := by
  have hA₀ : 0 < A₀ := lt_trans (by positivity) hgap
  -- Step 1: uniform coercivity (`eq:section4-uniform-coercivity-gap`, `eq:section2-subcritical-coercivity`)
  obtain ⟨B, hB, hbound⟩ :=
    SubcriticalOptimizerCompactness.eventual_energy_bound hR hgap hA U hU hmax
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  -- Step 2: Rellich: compactness of the critical energy ball in `L²`
  obtain ⟨V, hV, φ, hφ, hlim⟩ := (realSobolevBall_isCompact hd hB).tendsto_subseq
    (x := fun n => U (n + N)) (fun n => hN (n + N) (by omega))
  obtain ⟨ψ₁, hψ₁, hae⟩ := exists_subseq_tendsto_ae hlim
  set ψ : ℕ → ℕ := fun n => φ (ψ₁ n) + N with hψdef
  have hψ : StrictMono ψ := fun a b hab => by
    have := hφ (hψ₁ hab)
    simp only [hψdef]; omega
  have hψtop : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hmem : ∀ n, U (ψ n) ∈ realSobolevBall d B := fun n => hN (ψ n) (by simp only [hψdef]; omega)
  have hlimu : Tendsto (fun n => U (ψ n)) atTop (𝓝 V) := hlim.comp hψ₁.tendsto_atTop
  have haeu : ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => (U (ψ n) x).re) atTop (𝓝 (V x).re) := by
    filter_upwards [hae] with x hx
    exact (Complex.continuous_re.tendsto _).comp hx
  have hAdm : ∀ n, Admissible (U (ψ n)) := fun n => hU (ψ n)
  have hVadm : Admissible V := ⟨hV.2, hV.1.1⟩
  have hAn : Tendsto (fun n => A (ψ n)) atTop (𝓝 A₀) := hA.comp hψtop
  have hvaln : Tendsto (fun n => functional (A (ψ n)) (U (ψ n))) atTop (𝓝 0) := hval.comp hψtop
  -- Step 3: uniform exponential moments
  have hmom : ∀ p : ℝ, 0 < p → ∀ n, ∫ x, Real.exp (p * (U (ψ n) x).re) ∂torusMeasure d ≤
      Real.exp (p ^ 2 * B / (4 * b) + Real.log Ab) := by
    intro p hp n
    refine (integral_exp_upper hR (hAdm n) hp).trans (Real.exp_le_exp.2 ?_)
    have h1 : criticalEnergy (U (ψ n)) ≤ B := (hmem n).1.2
    have h2 : p ^ 2 * criticalEnergy (U (ψ n)) / (4 * b) ≤ p ^ 2 * B / (4 * b) := by
      gcongr
    linarith
  -- Step 4: Vitali
  have hZ : Tendsto (fun n => partition (U (ψ n))) atTop (𝓝 (partition V)) := by
    unfold partition
    refine tendsto_integral_of_sq_bound (f := fun n x => Real.exp ((U (ψ n) x).re))
      (g := fun x => Real.exp ((V x).re)) (fun n => ?_) (fun n => ?_)
      (Real.exp (2 ^ 2 * B / (4 * b) + Real.log Ab)) (fun n => ?_) ?_ ?_
    · simpa using aestronglyMeasurable_exp_re (U (ψ n)) 1
    · have := rough_integrable hR (hAdm n) (p := 2) (by norm_num)
      refine this.congr (Eventually.of_forall fun x => ?_)
      exact (exp_re_sq _ x).symm
    · have := hmom 2 (by norm_num) n
      calc ∫ x, Real.exp ((U (ψ n) x).re) ^ 2 ∂torusMeasure d
          = ∫ x, Real.exp (2 * (U (ψ n) x).re) ∂torusMeasure d :=
            integral_congr_ae (Eventually.of_forall fun x => exp_re_sq _ x)
        _ ≤ _ := this
    · simpa using partition_integrable hR hVadm
    · filter_upwards [haeu] with x hx
      exact (Real.continuous_exp.tendsto _).comp hx
  -- Step 5: energies and the maximizing identity
  set E : ℕ → ℝ := fun n => criticalEnergy (U (ψ n)) with hE
  set Z : ℕ → ℝ := fun n => partition (U (ψ n)) with hZdef
  have hZpos : 0 < partition V := partition_pos hR hVadm
  have hlogZ : Tendsto (fun n => Real.log (Z n)) atTop (𝓝 (Real.log (partition V))) :=
    (Real.continuousAt_log hZpos.ne').tendsto.comp hZ
  have hApos : ∀ᶠ n in atTop, 0 < A (ψ n) := hAn.eventually (lt_mem_nhds hA₀)
  -- `E n = (log Z n - value n) / A n` eventually
  have hEeq : ∀ᶠ n in atTop, E n =
      (Real.log (Z n) - functional (A (ψ n)) (U (ψ n))) / A (ψ n) := by
    filter_upwards [hApos] with n hn
    rw [functional_eq]
    field_simp
    ring
  set e : ℝ := Real.log (partition V) / A₀ with he
  have hEtend : Tendsto E atTop (𝓝 e) := by
    have h := (hlogZ.sub hvaln).div hAn hA₀.ne'
    rw [sub_zero] at h
    exact h.congr' (hEeq.mono fun n hn => hn.symm)
  -- lower semicontinuity: `‖V‖² ≤ e`
  have hVe : criticalEnergy V ≤ e := by
    by_contra hcon
    push Not at hcon
    set y : ℝ := (e + criticalEnergy V) / 2 with hy
    have hy1 : y < criticalEnergy V := by rw [hy]; linarith
    have hy2 : e < y := by rw [hy]; linarith
    have hlsc := (energy_lowerSemicontinuousOn d B) V hV y hy1
    have ht : Tendsto (fun n => U (ψ n)) atTop (𝓝[realSobolevBall d B] V) :=
      tendsto_nhdsWithin_iff.2 ⟨hlimu, Eventually.of_forall hmem⟩
    have h1 := ht.eventually hlsc
    have h2 := (tendsto_order.1 hEtend).2 y hy2
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    exact absurd hn1 (not_lt.2 hn2.le)
  -- every admissible `W` has `functional A₀ W ≤ 0`
  have hle0 : ∀ W : TorusL2 d, Admissible W → functional A₀ W ≤ 0 := by
    intro W hW
    have h1 : Tendsto (fun n => functional (A (ψ n)) W) atTop (𝓝 (functional A₀ W)) := by
      unfold functional
      exact tendsto_const_nhds.sub (hAn.mul_const _)
    exact le_of_tendsto_of_tendsto h1 hvaln
      (Eventually.of_forall fun n => hmax (ψ n) W hW)
  have hVge : 0 ≤ functional A₀ V := by
    rw [functional_eq]
    have : A₀ * criticalEnergy V ≤ A₀ * e := mul_le_mul_of_nonneg_left hVe hA₀.le
    have hAe : A₀ * e = Real.log (partition V) := by rw [he]; field_simp
    linarith
  have hV0 : functional A₀ V = 0 := le_antisymm (hle0 V hVadm) hVge
  -- the energy of the limit equals `e`
  have hEV : criticalEnergy V = e := by
    have h := hV0
    rw [functional_eq] at h
    have hAe : A₀ * e = Real.log (partition V) := by rw [he]; field_simp
    have : A₀ * criticalEnergy V = A₀ * e := by linarith
    exact mul_left_cancel₀ hA₀.ne' this
  have hEconv : Tendsto E atTop (𝓝 (criticalEnergy V)) := hEV ▸ hEtend
  -- Step 6: strong convergence (Radon--Riesz in the weighted `ℓ²`)
  have hw : ∀ k : Frequency d, 0 ≤ frequencyRadius k ^ d := fun k =>
    pow_nonneg (Real.sqrt_nonneg _) _
  have hsum : ∀ W : TorusL2 d, CriticalSobolev W →
      Summable fun k => frequencyRadius k ^ d * ‖fourierIsometry d W k‖ ^ 2 := fun W hW => hW.2
  have hrr := radon_riesz (fun k : Frequency d => frequencyRadius k ^ d) hw
    (fun n k => fourierIsometry d (U (ψ n)) k) (fun k => fourierIsometry d V k)
    (fun n => hsum _ (hAdm n).2) (hsum _ hVadm.2) (tendsto_coefficient hlimu) hEconv
  have hstrong : Tendsto (fun n => criticalEnergy (U (ψ n) - V)) atTop (𝓝 0) := by
    refine hrr.congr fun n => ?_
    unfold criticalEnergy coefficientEnergy
    refine tsum_congr fun k => ?_
    simp only [weightedSquare, map_sub, lp.coeFn_sub, Pi.sub_apply]
  exact ⟨B, V, ψ, hB, hψ, hV, hmem, hlimu, haeu, hmom, hZ, hV0,
    fun W hW => hV0 ▸ hle0 W hW, hEconv, hstrong⟩

end BecknerOnofri.V2.Reaudit.Compactness
