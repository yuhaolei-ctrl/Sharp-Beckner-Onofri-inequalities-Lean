module

public import BecknerOnofri.V2.Reaudit.Sobolev.Reduction

@[expose] public section

/-! # Taylor expansions in the Banach algebra `H^s(𝕋^d)`, `s > d/2`

Native `H^s` expansions used in the proof of `lem:section5-quartic-reduction` (S054):

* `exp_taylor`: `e^u = Σ_{k<N} u^k / k! + O(‖u‖^N)` in `H^s` (Mathlib's Taylor formula for the
  analytic map `NormedSpace.exp` on the Banach algebra `Hs d s`);
* `gibbs_second_order`: for mean-zero `u`,
  `ρ_u = 1 + u + ½ (u² - ∫u²) + O(‖u‖³)` in the `H^s` norm (the second line of
  `eq:section5-complement-Taylor-expansions`, before substituting the slaved `w`);
* `logZ_taylor`: for mean-zero `u`,
  `log Z(u) = ½∫u² + ⅙∫u³ + 1/24 ∫u⁴ - ⅛ (∫u²)² + O(‖u‖⁵)` (`eq:section5-log-partition-taylor`).

All remainders are estimated in the (constant multiple of the) `H^s` norm of `Hs d s`, using
only the Banach-algebra inequality `‖uv‖ ≤ ‖u‖‖v‖` and the analyticity of `exp`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

theorem val_pow' (u : Hs d s) (n : ℕ) : (u ^ n).val = u.val ^ n := by
  have := map_pow (Hs.toSpaceAlg (d := d) (s := s)) u n
  simpa only [Hs.toSpaceAlg_apply] using this

/-- The filter of mean-zero elements of `H^s` tending to `0`. -/
def meanZeroNhds (d : ℕ) (s : ℝ) [SobolevIndex d s] : Filter (Hs d s) :=
  𝓝[{u : Hs d s | Hs.meanCLM d s u = 0}] 0

theorem meanZeroNhds_le : meanZeroNhds d s ≤ 𝓝 (0 : Hs d s) := nhdsWithin_le_nhds

theorem mem_meanZeroNhds_self : {u : Hs d s | Hs.meanCLM d s u = 0} ∈ meanZeroNhds d s :=
  self_mem_nhdsWithin

theorem meanZeroNhds_eventually_mean :
    ∀ᶠ u in meanZeroNhds d s, Hs.meanCLM d s u = 0 :=
  mem_meanZeroNhds_self

theorem tendsto_meanZeroNhds_zero : Tendsto (fun u : Hs d s => u) (meanZeroNhds d s) (𝓝 0) :=
  meanZeroNhds_le

/-! ## The Taylor formula for `exp` -/

/-- **Taylor formula for `exp` in `H^s`**: `e^u = Σ_{k<N} u^k/k! + O(‖u‖^N)`. -/
theorem exp_taylor (N : ℕ) :
    (fun u : Hs d s => NormedSpace.exp u - ∑ k ∈ Finset.range N, ((k.factorial : ℝ)⁻¹) • u ^ k)
      =O[𝓝 (0 : Hs d s)] (fun u => ‖u‖ ^ N) := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := Hs d s)).isBigO_sub_partialSum_pow N
  refine h.congr' (Eventually.of_forall fun u => ?_) (Eventually.of_forall fun u => rfl)
  simp only [zero_add, FormalMultilinearSeries.partialSum, NormedSpace.expSeries_apply_eq]

/-! ## The partition function -/

/-- The moment `m_k(u) = ∫ u^k`. -/
def pk (d : ℕ) (s : ℝ) [SobolevIndex d s] (k : ℕ) (u : Hs d s) : ℝ := Hs.meanCLM d s (u ^ k)

theorem pk_smul (k : ℕ) (t : ℝ) (u : Hs d s) : pk d s k (t • u) = t ^ k * pk d s k u := by
  unfold pk
  rw [smul_pow, map_smul, smul_eq_mul]

theorem pk_isBigO (k : ℕ) (hk : 1 ≤ k) :
    (fun u : Hs d s => pk d s k u) =O[𝓝 (0 : Hs d s)] (fun u => ‖u‖ ^ k) := by
  apply IsBigO.of_bound ‖Hs.meanCLM d s‖
  refine Eventually.of_forall fun u => ?_
  have h1 : ‖pk d s k u‖ ≤ ‖Hs.meanCLM d s‖ * ‖u ^ k‖ := (Hs.meanCLM d s).le_opNorm _
  have h2 : ‖u ^ k‖ ≤ ‖u‖ ^ k := norm_pow_le' u hk
  rw [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖ ^ k)]
  calc ‖pk d s k u‖ ≤ ‖Hs.meanCLM d s‖ * ‖u ^ k‖ := h1
    _ ≤ ‖Hs.meanCLM d s‖ * ‖u‖ ^ k := by gcongr

theorem meanCLM_one : Hs.meanCLM d s (1 : Hs d s) = 1 := by
  rw [Hs.meanCLM_apply, Hs.val_one, mean_one]

theorem meanCLM_exp_sum_five (u : Hs d s) (hu : Hs.meanCLM d s u = 0) :
    Hs.meanCLM d s (∑ k ∈ Finset.range 5, ((k.factorial : ℝ)⁻¹) • u ^ k) =
      1 + pk d s 2 u / 2 + pk d s 3 u / 6 + pk d s 4 u / 24 := by
  rw [map_sum]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, map_smul, pow_zero,
    pow_one, meanCLM_one, hu, smul_eq_mul]
  simp only [pk, Nat.factorial]
  norm_num
  ring

/-- **Taylor formula for the partition function** on mean-zero potentials:
`Z(u) = 1 + ½∫u² + ⅙∫u³ + 1/24 ∫u⁴ + O(‖u‖⁵)`. -/
theorem partition_taylor :
    (fun u : Hs d s => Hs.partition u - (1 + pk d s 2 u / 2 + pk d s 3 u / 6 + pk d s 4 u / 24))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 5) := by
  have h0 := ((exp_taylor (d := d) (s := s) 5).mono meanZeroNhds_le)
  have h1 := ((Hs.meanCLM d s).isBigO_comp (fun u : Hs d s => NormedSpace.exp u -
    ∑ k ∈ Finset.range 5, ((k.factorial : ℝ)⁻¹) • u ^ k) (meanZeroNhds d s)).trans h0
  refine h1.congr' ?_ (Eventually.of_forall fun u => rfl)
  filter_upwards [meanZeroNhds_eventually_mean (d := d) (s := s)] with u hu
  rw [map_sub, meanCLM_exp_sum_five u hu]
  rfl

/-! ## The logarithm of the partition function -/

/-- `log Z(u)`. -/
def logZ (u : Hs d s) : ℝ := Real.log (Hs.partition u)

theorem norm_pow_isBigO_of_le {E : Type*} [NormedAddCommGroup E] {m n : ℕ} (h : n ≤ m) :
    (fun x : E => ‖x‖ ^ m) =O[𝓝 0] (fun x => ‖x‖ ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ ≤ 1 := le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hx)
  rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _),
    Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) _), one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg x) hx' h

/-- The cubic remainder of the logarithm: `log(1+x) = x - x²/2 + O(|x|³)`. -/
theorem log_remainder_isBigO :
    (fun x : ℝ => Real.log (1 + x) - x + x ^ 2 / 2) =O[𝓝 (0 : ℝ)] (fun x => ‖x‖ ^ 3) := by
  apply IsBigO.of_bound 2
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
  have hx' : |x| < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hx
  have hlt : |-x| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, abs_neg,
    sub_neg_eq_add] at h
  have h1 : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ |x| ^ 3 := by positivity
    nlinarith
  have e : (-x) ^ (0 + 1) / ((0 : ℕ) + 1) + (-x) ^ (1 + 1) / ((1 : ℕ) + 1) + Real.log (1 + x) =
      Real.log (1 + x) - x + x ^ 2 / 2 := by
    push_cast
    ring
  rw [e] at h
  simp only [Real.norm_eq_abs, abs_pow, abs_abs]
  linarith [h.trans h1]

theorem isBigO_div_const' {α F : Type*} [Norm F] {l : Filter α} {f : α → ℝ} {g : α → F}
    (h : f =O[l] g) (c : ℝ) : (fun x => f x / c) =O[l] g := by
  simpa only [div_eq_inv_mul] using h.const_mul_left c⁻¹

theorem partition_tendsto : Tendsto (fun u : Hs d s => Hs.partition u) (𝓝 0) (𝓝 1) := by
  have h := (Hs.partition_analytic (0 : Hs d s)).continuousAt.tendsto
  simpa using h

theorem partition_sub_one_isBigO :
    (fun u : Hs d s => Hs.partition u - 1) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 2) := by
  have h2 := (pk_isBigO (d := d) (s := s) 2 (by norm_num)).mono meanZeroNhds_le
  have h3 := ((pk_isBigO (d := d) (s := s) 3 (by norm_num)).mono meanZeroNhds_le).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 3) (n := 2) (by norm_num)).mono meanZeroNhds_le)
  have h4 := ((pk_isBigO (d := d) (s := s) 4 (by norm_num)).mono meanZeroNhds_le).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 4) (n := 2) (by norm_num)).mono meanZeroNhds_le)
  have h5 := (partition_taylor (d := d) (s := s)).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 5) (n := 2) (by norm_num)).mono meanZeroNhds_le)
  have hh := (((isBigO_div_const' h2 2).add (isBigO_div_const' h3 6)).add (isBigO_div_const' h4 24)).add h5
  refine hh.congr_left fun u => ?_
  ring

/-- **`eq:section5-log-partition-taylor`** in `H^s`: for mean-zero `u` near zero,
`log Z(u) = ½∫u² + ⅙∫u³ + 1/24 ∫u⁴ - ⅛ (∫u²)² + O(‖u‖⁵_{H^s})`. -/
theorem logZ_taylor :
    (fun u : Hs d s => logZ u - (pk d s 2 u / 2 + pk d s 3 u / 6 + pk d s 4 u / 24 -
        (pk d s 2 u) ^ 2 / 8)) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 5) := by
  set ε : Hs d s → ℝ := fun u => Hs.partition u - 1 with hε
  have hεO := partition_sub_one_isBigO (d := d) (s := s)
  have hεt : Tendsto ε (meanZeroNhds d s) (𝓝 0) := by
    have := (partition_tendsto (d := d) (s := s)).mono_left meanZeroNhds_le
    simpa [hε] using this.sub_const 1
  have hR := (log_remainder_isBigO.comp_tendsto hεt)
  have hR6 : (fun u : Hs d s => Real.log (1 + ε u) - ε u + ε u ^ 2 / 2)
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 5) := by
    have h1 : (fun u => ‖ε u‖ ^ 3) =O[meanZeroNhds d s] (fun u : Hs d s => (‖u‖ ^ 2) ^ 3) :=
      (hεO.norm_left).pow 3
    have h2 : (fun u : Hs d s => (‖u‖ ^ 2) ^ 3) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 5) := by
      have := (norm_pow_isBigO_of_le (E := Hs d s) (m := 6) (n := 5) (by norm_num)).mono
        (meanZeroNhds_le (d := d) (s := s))
      refine this.congr_left fun u => ?_
      ring
    exact (hR.trans h1).trans h2
  have h2 := (pk_isBigO (d := d) (s := s) 2 (by norm_num)).mono meanZeroNhds_le
  -- `ε - P₃ = O(‖u‖⁵)`
  have ht1 := partition_taylor (d := d) (s := s)
  -- `ε - ½ m₂ = O(‖u‖³)`
  have h3 := ((pk_isBigO (d := d) (s := s) 3 (by norm_num)).mono meanZeroNhds_le)
  have h4 := ((pk_isBigO (d := d) (s := s) 4 (by norm_num)).mono meanZeroNhds_le).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 4) (n := 3) (by norm_num)).mono meanZeroNhds_le)
  have h5 := (partition_taylor (d := d) (s := s)).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 5) (n := 3) (by norm_num)).mono meanZeroNhds_le)
  have hA : (fun u : Hs d s => ε u - pk d s 2 u / 2) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
    have hh := ((isBigO_div_const' h3 6).add (isBigO_div_const' h4 24)).add h5
    refine hh.congr_left fun u => ?_
    simp only [hε]
    ring
  have hB : (fun u : Hs d s => ε u + pk d s 2 u / 2) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 2) :=
    hεO.add (isBigO_div_const' h2 2)
  have hAB : (fun u : Hs d s => (ε u - pk d s 2 u / 2) * (ε u + pk d s 2 u / 2))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 5) := by
    have := hA.mul hB
    refine this.congr_right fun u => ?_
    ring
  have hfin := (ht1.sub (hAB.const_mul_left (1 / 2 : ℝ))).add hR6
  refine hfin.congr_left fun u => ?_
  simp only [logZ, hε]
  have : Real.log (Hs.partition u) = Real.log (1 + (Hs.partition u - 1)) := by ring_nf
  rw [this]
  ring

/-! ## Second-order expansion of the Gibbs map -/

theorem partition_sub_pk_isBigO :
    (fun u : Hs d s => Hs.partition u - 1 - pk d s 2 u / 2) =O[meanZeroNhds d s]
      (fun u => ‖u‖ ^ 3) := by
  have h3 := ((pk_isBigO (d := d) (s := s) 3 (by norm_num)).mono meanZeroNhds_le)
  have h4 := ((pk_isBigO (d := d) (s := s) 4 (by norm_num)).mono meanZeroNhds_le).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 4) (n := 3) (by norm_num)).mono meanZeroNhds_le)
  have h5 := (partition_taylor (d := d) (s := s)).trans
    ((norm_pow_isBigO_of_le (E := Hs d s) (m := 5) (n := 3) (by norm_num)).mono meanZeroNhds_le)
  have hh := ((isBigO_div_const' h3 6).add (isBigO_div_const' h4 24)).add h5
  refine hh.congr_left fun u => ?_
  ring

/-- `Z(u)^{-1} - 1 = O(‖u‖²)` on mean-zero potentials. -/
theorem partition_inv_sub_one_isBigO :
    (fun u : Hs d s => (Hs.partition u)⁻¹ - 1) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 2) := by
  have hZ : Tendsto (fun u : Hs d s => (Hs.partition u)⁻¹) (meanZeroNhds d s) (𝓝 1) := by
    have := ((partition_tendsto (d := d) (s := s)).mono_left meanZeroNhds_le).inv₀ (by norm_num)
    simpa using this
  have hb : (fun u : Hs d s => (Hs.partition u)⁻¹) =O[meanZeroNhds d s] (fun _ => (1 : ℝ)) :=
    hZ.isBigO_one ℝ
  have := hb.mul (partition_sub_one_isBigO (d := d) (s := s))
  refine (this.const_mul_left (-1 : ℝ)).congr' ?_ ?_
  · refine Eventually.of_forall fun u => ?_
    have hp := (Hs.partition_pos u).ne'
    simp only
    field_simp
    ring
  · exact Eventually.of_forall fun u => by simp

theorem partition_inv_cubic :
    (fun u : Hs d s => (Hs.partition u)⁻¹ - 1 + pk d s 2 u / 2) =O[meanZeroNhds d s]
      (fun u => ‖u‖ ^ 3) := by
  have h1 := partition_sub_pk_isBigO (d := d) (s := s)
  have h2 := (partition_inv_sub_one_isBigO (d := d) (s := s)).mul
    (partition_sub_one_isBigO (d := d) (s := s))
  have h2' : (fun u : Hs d s => ((Hs.partition u)⁻¹ - 1) * (Hs.partition u - 1))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
    refine h2.trans ?_
    have := (norm_pow_isBigO_of_le (E := Hs d s) (m := 4) (n := 3) (by norm_num)).mono
      (meanZeroNhds_le (d := d) (s := s))
    refine this.congr_left fun u => ?_
    ring
  have hh := (h1.const_mul_left (-1 : ℝ)).sub h2'
  refine (hh.congr_left fun u => ?_)
  have hp := (Hs.partition_pos u).ne'
  field_simp
  ring

/-- **Second-order expansion of the Gibbs map in `H^s`** (the second line of
`eq:section5-complement-Taylor-expansions`, before the slaved `w` is inserted): for mean-zero `u`,
`ρ_u = 1 + u + ½ (u² - ∫u²) + O(‖u‖³)` in the `H^s` norm. -/
theorem gibbs_second_order :
    (fun u : Hs d s => Hs.gibbs u - 1 - u - (1 / 2 : ℝ) • (u ^ 2 - pk d s 2 u • (1 : Hs d s)))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
  have hR := (exp_taylor (d := d) (s := s) 3).mono (meanZeroNhds_le (d := d) (s := s))
  set R : Hs d s → Hs d s := fun u => NormedSpace.exp u -
    ∑ k ∈ Finset.range 3, ((k.factorial : ℝ)⁻¹) • u ^ k with hRdef
  have hZ : Tendsto (fun u : Hs d s => (Hs.partition u)⁻¹) (meanZeroNhds d s) (𝓝 1) := by
    have := ((partition_tendsto (d := d) (s := s)).mono_left meanZeroNhds_le).inv₀ (by norm_num)
    simpa using this
  have hb : (fun u : Hs d s => (Hs.partition u)⁻¹) =O[meanZeroNhds d s] (fun _ => (1 : ℝ)) :=
    hZ.isBigO_one ℝ
  -- r • 1
  have t1 : (fun u : Hs d s => ((Hs.partition u)⁻¹ - 1 + pk d s 2 u / 2) • (1 : Hs d s))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
    have := (partition_inv_cubic (d := d) (s := s)).smul
      (isBigO_const_const (1 : Hs d s) (one_ne_zero' (ℝ)) (meanZeroNhds d s))
    simpa using this
  -- (Zinv - 1) • (u + u²/2)
  have hu1 : (fun u : Hs d s => u + (1 / 2 : ℝ) • u ^ 2) =O[meanZeroNhds d s] (fun u => ‖u‖) := by
    have a1 : (fun u : Hs d s => u) =O[meanZeroNhds d s] (fun u => ‖u‖) :=
      (isBigO_refl (fun u : Hs d s => u) _).congr_right (fun u => rfl) |>.trans
        (by exact Asymptotics.isBigO_norm_right.mpr (isBigO_refl _ _))
    have a2 : (fun u : Hs d s => u ^ 2) =O[meanZeroNhds d s] (fun u => ‖u‖) := by
      have : (fun u : Hs d s => u ^ 2) =O[𝓝 (0 : Hs d s)] (fun u => ‖u‖ ^ 2) := by
        apply IsBigO.of_bound 1
        refine Eventually.of_forall fun u => ?_
        rw [one_mul, Real.norm_of_nonneg (by positivity)]
        exact norm_pow_le' u (by norm_num)
      exact ((this.trans (norm_pow_isBigO_of_le (E := Hs d s) (m := 2) (n := 1) (by norm_num))).mono
        meanZeroNhds_le).congr_right (fun u => by simp)
    exact a1.add (a2.const_smul_left (1 / 2 : ℝ))
  have t2 : (fun u : Hs d s => ((Hs.partition u)⁻¹ - 1) • (u + (1 / 2 : ℝ) • u ^ 2))
      =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
    have := (partition_inv_sub_one_isBigO (d := d) (s := s)).smul hu1
    refine this.congr_right fun u => ?_
    simp only [smul_eq_mul]
    ring
  -- Zinv • R
  have t3 : (fun u : Hs d s => (Hs.partition u)⁻¹ • R u) =O[meanZeroNhds d s] (fun u => ‖u‖ ^ 3) := by
    have := hb.smul hR
    refine this.congr_right fun u => ?_
    simp
  refine ((t1.add t2).add t3).congr_left fun u => ?_
  simp only [Hs.gibbs, hRdef]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial, pow_zero,
    pow_one]
  norm_num
  module

end BecknerOnofri.V2.Reaudit.SobolevQuartic
