module

public import BecknerOnofri.V2.Onset.Tail
public import BecknerOnofri.RawAttainment
public import BecknerOnofri.OnsetContinuous
public import BecknerOnofri.FullHessianDecomposition

@[expose] public section

/-! # Compactness in every fixed Sobolev norm (Proposition 5.24, "Sobolev compactness")

A sequence of continuous mean-zero functions that is bounded in every `H^{(m+1)d}` has a
subsequence converging in every fixed `H^r` to a smooth function.  The proof combines the `L²`
(Rellich) compactness of critical Sobolev balls `Legacy...SubcriticalAttainment.realSobolevBall_isCompact`
with a Fatou argument and the tail splitting of `Tail.lean`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace BecknerOnofri.V2.Onset
open BecknerOnofri.HighDim Legacy.BecknerOnofri.TorusSobolev Legacy.BecknerOnofri.SubcriticalAttainment

/-- Pointwise tail splitting for abstract weights `w ≥ 1`. -/
theorem rpow_tail_le {w a : ℝ} (hw : 1 ≤ w) (ha : 0 ≤ a) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    {A : ℝ} (hA : 0 < A) :
    w ^ r * a ≤ A ^ r * a + A ^ (r - s) * (w ^ s * a) := by
  have hw0 : 0 < w := by linarith
  have h1 : 0 ≤ A ^ r * a := by positivity
  have h2 : 0 ≤ A ^ (r - s) * (w ^ s * a) := by positivity
  rcases le_or_gt w A with h | h
  · have : w ^ r ≤ A ^ r := Real.rpow_le_rpow hw0.le h hr
    nlinarith [mul_le_mul_of_nonneg_right this ha]
  · have e : w ^ r = w ^ s * w ^ (r - s) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have : w ^ (r - s) ≤ A ^ (r - s) := Real.rpow_le_rpow_of_nonpos hA h.le (by linarith)
    have h3 : w ^ r * a ≤ A ^ (r - s) * (w ^ s * a) := by
      rw [e]
      have := mul_le_mul_of_nonneg_right this (mul_nonneg (Real.rpow_nonneg hw0.le s) ha)
      nlinarith [this]
    linarith

/-- **Interpolation limit.**  If `∑ a_n → 0` and `∑ w^s a_n` stays bounded then `∑ w^r a_n → 0`
for `0 ≤ r < s`. -/
theorem tail_tendsto {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 1 ≤ w i) (a : ℕ → ι → ℝ)
    (ha : ∀ n i, 0 ≤ a n i) {r s K : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hsum0 : ∀ n, Summable (a n))
    (hlim : Tendsto (fun n => ∑' i, a n i) atTop (𝓝 0))
    (hsumS : ∀ n, Summable (fun i => w i ^ s * a n i))
    (hK : ∀ n, ∑' i, w i ^ s * a n i ≤ K) :
    (∀ n, Summable (fun i => w i ^ r * a n i)) ∧
      Tendsto (fun n => ∑' i, w i ^ r * a n i) atTop (𝓝 0) := by
  have hbound : ∀ A : ℝ, 0 < A → ∀ n, Summable (fun i => w i ^ r * a n i) ∧
      ∑' i, w i ^ r * a n i ≤ A ^ r * ∑' i, a n i + A ^ (r - s) * K := by
    intro A hA n
    have hmaj : Summable (fun i => A ^ r * a n i + A ^ (r - s) * (w i ^ s * a n i)) :=
      ((hsum0 n).mul_left _).add ((hsumS n).mul_left _)
    have hnn : ∀ i, 0 ≤ w i ^ r * a n i := fun i =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hw i]) _) (ha n i)
    have hsm : Summable (fun i => w i ^ r * a n i) :=
      Summable.of_nonneg_of_le hnn
        (fun i => rpow_tail_le (hw i) (ha n i) hr hrs.le hA) hmaj
    refine ⟨hsm, ?_⟩
    calc ∑' i, w i ^ r * a n i
        ≤ ∑' i, (A ^ r * a n i + A ^ (r - s) * (w i ^ s * a n i)) :=
          hsm.tsum_le_tsum (fun i => rpow_tail_le (hw i) (ha n i) hr hrs.le hA) hmaj
      _ = A ^ r * ∑' i, a n i + A ^ (r - s) * ∑' i, w i ^ s * a n i := by
          rw [Summable.tsum_add ((hsum0 n).mul_left _) ((hsumS n).mul_left _), tsum_mul_left,
            tsum_mul_left]
      _ ≤ A ^ r * ∑' i, a n i + A ^ (r - s) * K := by
          have : 0 ≤ A ^ (r - s) := Real.rpow_nonneg hA.le _
          nlinarith [hK n]
  refine ⟨fun n => (hbound 1 one_pos n).1, ?_⟩
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n => ?_, fun ε hε => ?_⟩
  · exact lt_of_lt_of_le hx (tsum_nonneg fun i =>
      mul_nonneg (Real.rpow_nonneg (by linarith [hw i]) _) (ha n i))
  · -- choose A large
    have ht : Tendsto (fun x : ℝ => x ^ (-(s - r))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have hKpos : 0 < |K| + 1 := by positivity
    obtain ⟨A, hAbig⟩ := ((ht.eventually (gt_mem_nhds (div_pos hε (by linarith : (0:ℝ) < 2 * (|K| + 1))
      ))).and (eventually_ge_atTop 1)).exists
    obtain ⟨hAsmall, hA1⟩ := hAbig
    have hA : 0 < A := by linarith
    have hrs' : r - s = -(s - r) := by ring
    have hArs : A ^ (r - s) * K < ε / 2 := by
      rw [hrs']
      calc A ^ (-(s - r)) * K ≤ A ^ (-(s - r)) * (|K| + 1) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hA.le _)
            linarith [le_abs_self K]
        _ < ε / (2 * (|K| + 1)) * (|K| + 1) :=
            mul_lt_mul_of_pos_right hAsmall hKpos
        _ = ε / 2 := by field_simp
    have hApos : 0 < A ^ r := Real.rpow_pos_of_pos hA r
    filter_upwards [hlim.eventually (gt_mem_nhds (div_pos hε (by linarith : (0:ℝ) < 2 * A ^ r)))]
      with n hn
    refine lt_of_le_of_lt (hbound A hA n).2 ?_
    have : A ^ r * ∑' i, a n i < ε / 2 := by
      have := mul_lt_mul_of_pos_left hn hApos
      calc A ^ r * ∑' i, a n i < A ^ r * (ε / (2 * A ^ r)) := this
        _ = ε / 2 := by field_simp
    linarith

theorem coeff_sq_hasSum {d : ℕ} (U V : TorusL2 d) :
    HasSum (fun k : Frequency d => ‖fourierIsometry d U k - fourierIsometry d V k‖ ^ 2)
      (‖U - V‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (fourierIsometry d (U - V))
  have h' : HasSum (fun k : Frequency d => ‖fourierIsometry d (U - V) k‖ ^ 2)
      (‖fourierIsometry d (U - V)‖ ^ 2) := by simpa using h
  rw [LinearIsometryEquiv.norm_map] at h'
  simpa [map_sub] using h'

theorem coeff_sq_tendsto {d : ℕ} (U : ℕ → TorusL2 d) (V : TorusL2 d)
    (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => ∑' k : Frequency d, ‖fourierIsometry d (U n) k - fourierIsometry d V k‖ ^ 2)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ‖U n - V‖) atTop (𝓝 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp h)
  have h2 := h1.pow 2
  simp only [zero_pow two_ne_zero] at h2
  refine h2.congr fun n => ?_
  exact (coeff_sq_hasSum (U n) V).tsum_eq.symm

theorem coeff_pointwise_tendsto {d : ℕ} (U : ℕ → TorusL2 d) (V : TorusL2 d)
    (h : Tendsto U atTop (𝓝 V)) (k : Frequency d) :
    Tendsto (fun n => fourierIsometry d (U n) k) atTop (𝓝 (fourierIsometry d V k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := coeff_sq_tendsto U V h
  have hle : ∀ n, ‖fourierIsometry d (U n) k - fourierIsometry d V k‖ ^ 2 ≤
      ∑' k : Frequency d, ‖fourierIsometry d (U n) k - fourierIsometry d V k‖ ^ 2 :=
    fun n => (coeff_sq_hasSum (U n) V).summable.le_tsum k (fun _ _ => sq_nonneg _)
  have h3 : Tendsto (fun n => ‖fourierIsometry d (U n) k - fourierIsometry d V k‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hle h1
  have h4 := h3.sqrt
  simp only [Real.sqrt_zero] at h4
  refine h4.congr fun n => ?_
  exact Real.sqrt_sq (norm_nonneg _)


/-- **Fatou for weighted `ℓ²` sums.** -/
theorem fatou_weighted {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℕ → ι → ℂ) (C : ι → ℂ)
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (C i))) {Bd : ℝ}
    (hbd : ∀ n, Summable (fun i => w i * ‖c n i‖ ^ 2) ∧ ∑' i, w i * ‖c n i‖ ^ 2 ≤ Bd) :
    Summable (fun i => w i * ‖C i‖ ^ 2) ∧ ∑' i, w i * ‖C i‖ ^ 2 ≤ Bd := by
  have hfin : ∀ F : Finset ι, ∑ i ∈ F, w i * ‖C i‖ ^ 2 ≤ Bd := by
    intro F
    have hlim : Tendsto (fun n => ∑ i ∈ F, w i * ‖c n i‖ ^ 2) atTop
        (𝓝 (∑ i ∈ F, w i * ‖C i‖ ^ 2)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      exact ((hc i).norm.pow 2).const_mul (w i)
    refine le_of_tendsto' hlim fun n => ?_
    exact ((hbd n).1.sum_le_tsum F (fun i _ => mul_nonneg (hw i) (sq_nonneg _))).trans (hbd n).2
  have hnn : 0 ≤ fun i => w i * ‖C i‖ ^ 2 := fun i => mul_nonneg (hw i) (sq_nonneg _)
  have hs := summable_of_sum_le hnn hfin
  exact ⟨hs, Real.tsum_le_of_sum_le hnn hfin⟩

theorem toL2_fourier {d : ℕ} (u : ContinuousGibbs.Space d) (k : Frequency d) :
    fourierIsometry d (ContinuousFirstShell.toL2 d u) k = fourierCoeff ⇑u k := by
  have hmem : MemLp (⇑u) 2 (torusMeasure d) :=
    ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ u
  have : ContinuousFirstShell.toL2 d u = Bridge.potentialLp ⇑u hmem :=
    Lp.ext ((ContinuousFirstShell.toL2_ae u).trans (Bridge.potentialLp_ae _ hmem).symm)
  rw [this, Bridge.potentialLp_fourier]

theorem real_fourier {d : ℕ} (V : TorusL2 d) (hV : RealPotential V) (k : Frequency d) :
    fourierIsometry d V k = fourierCoeff (RawAttainment.realValue V) k := by
  conv_lhs => rw [← RawAttainment.potentialLp_realValue V hV]
  exact Bridge.potentialLp_fourier _ _ k

theorem sobolevTerm_mono {d : ℕ} {s s' : ℝ} (h : s ≤ s') (u : Torus d → ℝ) (k : Frequency d) :
    sobolevTerm s u k ≤ sobolevTerm s' u k := by
  unfold sobolevTerm
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (2 * Real.pi * frequencyLength k)]) h

theorem sobolevNorm_sq_eq_tsum {d : ℕ} {s : ℝ} (u : Torus d → ℝ)
    (_h : Summable (sobolevTerm s u)) : sobolevNorm s u ^ 2 = ∑' k, sobolevTerm s u k := by
  unfold sobolevNorm
  exact Real.sq_sqrt (tsum_nonneg fun k => by rw [sobolevTerm_eq]; positivity)

/-- **Compactness in every fixed Sobolev norm.**  A sequence of continuous mean-zero critical
functions with bounded critical energy and bounded in every `H^{(m+1)d}` has a subsequence converging
in every `H^r` (`r ≥ 0`) to a smooth function. -/
theorem sobolev_subsequence_limit {d : ℕ} (hd : 0 < d) (B : ℕ → ℝ) (E : ℝ)
    (u : ℕ → ContinuousGibbs.Space d)
    (hu : ∀ n, InCriticalSobolev ⇑(u n)) (hm : ∀ n, MeanZero ⇑(u n))
    (hE : ∀ n, criticalEnergy (ContinuousFirstShell.toL2 d (u n)) ≤ E)
    (hb : ∀ n (m : ℕ), InSobolev (((m : ℝ) + 1) * d) ⇑(u n) ∧
      sobolevNorm (((m : ℝ) + 1) * d) ⇑(u n) ≤ B m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : ContinuousGibbs.Space d, MeanZero ⇑v ∧
      (∀ s : ℝ, InSobolev s ⇑v) ∧ ∀ r : ℝ, 0 ≤ r →
        (∀ n, InSobolev r (⇑(u (φ n)) - ⇑v)) ∧
        Tendsto (fun n => sobolevNorm r (⇑(u (φ n)) - ⇑v)) atTop (𝓝 0) := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hE0 : 0 ≤ E := (energy_nonneg _).trans (hE 0)
  have hadm : ∀ n, Admissible (ContinuousFirstShell.toL2 d (u n)) := fun n =>
    OnsetContinuous.toL2_admissible hd (u n) (hu n) (hm n)
  have hmem : ∀ n, ContinuousFirstShell.toL2 d (u n) ∈ realSobolevBall d E := fun n =>
    ⟨⟨(hadm n).2, hE n⟩, (hadm n).1⟩
  obtain ⟨V, hV, φ, hφ, hlim⟩ := (realSobolevBall_isCompact hd hE0).tendsto_subseq hmem
  have hVadm : Admissible V := ⟨hV.2, hV.1.1⟩
  set U : ℕ → TorusL2 d := fun n => ContinuousFirstShell.toL2 d (u (φ n)) with hU
  have hlim' : Tendsto U atTop (𝓝 V) := hlim
  set c : ℕ → Frequency d → ℂ := fun n k => fourierIsometry d (U n) k with hcdef
  set C : Frequency d → ℂ := fun k => fourierIsometry d V k with hCdef
  have hc : ∀ n k, c n k = fourierCoeff ⇑(u (φ n)) k := fun n k => toL2_fourier _ k
  have hC : ∀ k, C k = fourierCoeff (RawAttainment.realValue V) k := real_fourier V hV.2
  set w : Frequency d → ℝ := fun k => 1 + (2 * Real.pi * frequencyLength k) ^ 2 with hw
  have hw1 : ∀ k, 1 ≤ w k := fun k => by
    simp only [hw]; nlinarith [sq_nonneg (2 * Real.pi * frequencyLength k)]
  have hw0 : ∀ k, 0 < w k := fun k => by linarith [hw1 k]
  -- Fatou
  have hfat : ∀ m : ℕ, Summable (fun k => w k ^ (((m : ℝ) + 1) * d) * ‖C k‖ ^ 2) ∧
      ∑' k, w k ^ (((m : ℝ) + 1) * d) * ‖C k‖ ^ 2 ≤ (B m) ^ 2 := by
    intro m
    refine fatou_weighted (fun k => w k ^ (((m : ℝ) + 1) * d))
      (fun k => Real.rpow_nonneg (hw0 k).le _) c C (coeff_pointwise_tendsto U V hlim') ?_
    intro n
    have hterm : ∀ k, w k ^ (((m : ℝ) + 1) * d) * ‖c n k‖ ^ 2 =
        sobolevTerm (((m : ℝ) + 1) * d) ⇑(u (φ n)) k := by
      intro k; rw [hc]; rfl
    have hsm : Summable (fun k => w k ^ (((m : ℝ) + 1) * d) * ‖c n k‖ ^ 2) := by
      simp only [hterm]; exact (hb (φ n) m).1.2
    refine ⟨hsm, ?_⟩
    have h1 : ∑' k, w k ^ (((m : ℝ) + 1) * d) * ‖c n k‖ ^ 2 =
        sobolevNorm (((m : ℝ) + 1) * d) ⇑(u (φ n)) ^ 2 := by
      rw [sobolevNorm_sq_eq_tsum _ (hb (φ n) m).1.2]
      exact tsum_congr hterm
    rw [h1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb (φ n) m).2 2
  -- the limit function
  set v₀ : Torus d → ℝ := RawAttainment.realValue V with hv₀
  have hv₀mem : MemLp v₀ 2 (torusMeasure d) := RawAttainment.realValue_memLp V
  have hv₀S : ∀ m : ℕ, Summable (sobolevTerm (((m : ℝ) + 1) * d) v₀) := by
    intro m
    refine ((hfat m).1).congr fun k => ?_
    rw [hC]; rfl
  have hv₀H : InSobolev (d : ℝ) v₀ := by
    refine ⟨hv₀mem, ?_⟩
    simpa using hv₀S 0
  obtain ⟨v, hvae, hvS, -⟩ := SobolevEmbedding.exists_continuous_representative hd (by linarith : (d : ℝ) / 2 < d) v₀ hv₀H
  have hvC : ∀ k, fourierCoeff ⇑v k = C k := fun k => by
    rw [hC]
    unfold HighDim.fourierCoeff
    apply integral_congr_ae
    filter_upwards [hvae] with x hx
    rw [hx]
  have hvmem : MemLp (⇑v) 2 (torusMeasure d) := ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ v
  have hvm : ∀ m : ℕ, Summable (sobolevTerm (((m : ℝ) + 1) * d) ⇑v) := by
    intro m
    rw [OnsetRaw.sobolevTerm_congr_ae hvae]
    exact hv₀S m
  have hvall : ∀ s : ℝ, InSobolev s ⇑v := by
    intro s
    obtain ⟨m, hm'⟩ := exists_nat_ge (s / d)
    refine ⟨hvmem, ?_⟩
    refine Summable.of_nonneg_of_le (fun k => by rw [sobolevTerm_eq]; positivity)
      (fun k => sobolevTerm_mono ?_ ⇑v k) (hvm m)
    have : s ≤ m * d := by rwa [div_le_iff₀ hdpos] at hm'
    nlinarith
  have hvmean : MeanZero ⇑v := by
    have h0 := RawAttainment.realValue_meanZero V hVadm
    change ∫ x, v x ∂torusMeasure d = 0
    rw [integral_congr_ae hvae]
    exact h0
  refine ⟨φ, hφ, v, hvmean, hvall, fun r hr => ?_⟩
  -- interpolation
  obtain ⟨m, hm'⟩ := exists_nat_gt (r / d)
  have hrs : r < ((m : ℝ) + 1) * d := by
    have : r < m * d := by rwa [div_lt_iff₀ hdpos] at hm'
    nlinarith
  set s : ℝ := ((m : ℝ) + 1) * d with hs
  set a : ℕ → Frequency d → ℝ := fun n k => ‖c n k - C k‖ ^ 2 with ha
  have ha0 : ∀ n k, 0 ≤ a n k := fun n k => sq_nonneg _
  have hsum0 : ∀ n, Summable (a n) := fun n => (coeff_sq_hasSum (U n) V).summable
  have hlim0 : Tendsto (fun n => ∑' k, a n k) atTop (𝓝 0) := coeff_sq_tendsto U V hlim'
  have hmaj : ∀ n k, w k ^ s * a n k ≤
      2 * (w k ^ s * ‖c n k‖ ^ 2 + w k ^ s * ‖C k‖ ^ 2) := by
    intro n k
    have h := mul_le_mul_of_nonneg_left (FullHessianDecomposition.norm_sub_square_le (c n k) (C k))
      (Real.rpow_nonneg (hw0 k).le s)
    simp only [ha]
    nlinarith [h]
  have hcS : ∀ n, Summable (fun k => w k ^ s * ‖c n k‖ ^ 2) ∧
      ∑' k, w k ^ s * ‖c n k‖ ^ 2 ≤ (B m) ^ 2 := by
    intro n
    have hterm : ∀ k, w k ^ s * ‖c n k‖ ^ 2 = sobolevTerm s ⇑(u (φ n)) k := by
      intro k; rw [hc]; rfl
    have hsm : Summable (fun k => w k ^ s * ‖c n k‖ ^ 2) := by
      simp only [hterm]; exact (hb (φ n) m).1.2
    refine ⟨hsm, ?_⟩
    have h1 : ∑' k, w k ^ s * ‖c n k‖ ^ 2 = sobolevNorm s ⇑(u (φ n)) ^ 2 := by
      rw [sobolevNorm_sq_eq_tsum _ (hb (φ n) m).1.2]
      exact tsum_congr hterm
    rw [h1]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hb (φ n) m).2 2
  have hmajS : ∀ n, Summable (fun k => 2 * (w k ^ s * ‖c n k‖ ^ 2 + w k ^ s * ‖C k‖ ^ 2)) :=
    fun n => ((hcS n).1.add (hfat m).1).mul_left 2
  have hsumS : ∀ n, Summable (fun k => w k ^ s * a n k) := fun n =>
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (hw0 k).le s) (ha0 n k)) (hmaj n) (hmajS n)
  have hK : ∀ n, ∑' k, w k ^ s * a n k ≤ 4 * (B m) ^ 2 := by
    intro n
    calc ∑' k, w k ^ s * a n k
        ≤ ∑' k, 2 * (w k ^ s * ‖c n k‖ ^ 2 + w k ^ s * ‖C k‖ ^ 2) :=
          (hsumS n).tsum_le_tsum (hmaj n) (hmajS n)
      _ = 2 * (∑' k, w k ^ s * ‖c n k‖ ^ 2 + ∑' k, w k ^ s * ‖C k‖ ^ 2) := by
          rw [tsum_mul_left, Summable.tsum_add (hcS n).1 (hfat m).1]
      _ ≤ 4 * (B m) ^ 2 := by nlinarith [(hcS n).2, (hfat m).2]
  obtain ⟨hS, hT⟩ := tail_tendsto w hw1 a ha0 hr hrs hsum0 hlim0 hsumS hK
  have hdiff : ∀ n k, sobolevTerm r (⇑(u (φ n)) - ⇑v) k = w k ^ r * a n k := by
    intro n k
    unfold sobolevTerm
    rw [FullHessianDecomposition.fourierCoeff_sub _ _
      (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (u (φ n))) hvmem, hvC, ← hc]
  have hmemd : ∀ n, MemLp (⇑(u (φ n)) - ⇑v) 2 (torusMeasure d) := fun n =>
    (ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ (u (φ n))).sub hvmem
  refine ⟨fun n => ⟨hmemd n, ?_⟩, ?_⟩
  · have hfun : sobolevTerm r (⇑(u (φ n)) - ⇑v) = fun k => w k ^ r * a n k := funext (hdiff n)
    rw [hfun]
    exact hS n
  · have := hT.sqrt
    simp only [Real.sqrt_zero] at this
    refine this.congr fun n => ?_
    simp only [sobolevNorm, hdiff]

end BecknerOnofri.V2.Onset
