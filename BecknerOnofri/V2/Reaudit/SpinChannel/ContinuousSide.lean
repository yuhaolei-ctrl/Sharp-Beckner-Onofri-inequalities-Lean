module

public import BecknerOnofri.V2.Reaudit.SpinChannel.Conditional
public import BecknerOnofri.V2.Channel.Budget
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-!
# The continuous side of the entropy comparison, under the joint law

From the chain rule `Ent(ρ) = ∑_i E[Ent(p_i(·|x_{<i}))]`, Lemma 5.16 at every conditioning value, and
Jensen's inequality for `E[r_{i,n}²] ≥ E[r_{i,n}]² = |ρ̂(ne_i)|²` and `E[ψ(t_i)] ≥ ψ(E t_i)`, all expectations
being taken with respect to the joint law `P_ρ`, to `eq:section5-channel-continuous-entropy`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.ConditionalEntropy BecknerOnofri.V2.Channel

/-- **Jensen's inequality under the joint law.** -/
theorem jensen_jointLaw (ρ : ProbabilityDensity 12) {a b : ℝ} {u : JointSpace → ℝ} (hu : BM u)
    (hr : ∀ ω, u ω ∈ Icc a b) (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc a b))
    (hψ : ConvexOn ℝ (Icc a b) ψ) :
    ψ (∫ ω, u ω ∂jointLaw ρ) ≤ ∫ ω, ψ (u ω) ∂jointLaw ρ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.norm
  have hψu : BM (fun ω => ψ (u ω)) :=
    ⟨hc.domRestrict.measurable.comp (hu.1.subtype_mk (h := hr)), C,
      fun ω => hC (mem_image_of_mem (fun y => ‖ψ y‖) (hr ω))⟩
  exact hψ.map_integral_le hc isClosed_Icc (Filter.Eventually.of_forall hr)
    (hu.integrable _) (hψu.integrable _)

/-- The tower property `E[E[g(x_i) | x_{<i}]] = E[g(x_i)]`. -/
theorem integral_condInt (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12)
    {g : UnitAddCircle → ℝ} (hg : BMC g) :
    ∫ ω, condInt ρ.value i g ω.1 ∂jointLaw ρ = ∫ ω, g (ω.1 i) ∂jointLaw ρ := by
  have h1 := condExp_position ρ hρ i hg
  have h2 := integral_condExp (μ := jointLaw ρ) (sigmaPos_le i.val) (f := fun ω : JointSpace => g (ω.1 i))
  rw [integral_congr_ae h1] at h2
  exact h2

/-- `E[g(x_i)] = ∫ ρ g(x_i) dm`. -/
theorem integral_coord (ρ : ProbabilityDensity 12) (i : Fin 12) {g : UnitAddCircle → ℝ} (hg : BMC g) :
    ∫ ω, g (ω.1 i) ∂jointLaw ρ = ∫ x, ρ.value x * g (x i) ∂torusMeasure 12 :=
  integral_jointLaw_position ρ (hg.coord i)

/-- `E[r_{i,n}] = ∫ ρ cos(2πn x_i) dm = Re ρ̂(n e_i)`. -/
theorem integral_condInt_cos (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12)
    (n : ℕ) :
    ∫ ω, condInt ρ.value i (cosFn n) ω.1 ∂jointLaw ρ =
      ∫ x, ρ.value x * (fourier (n : ℤ) (x i)).re ∂torusMeasure 12 := by
  rw [integral_condInt ρ hρ i (bmc_cosFn n), integral_coord ρ i (bmc_cosFn n)]
  rfl

theorem BM.condInt (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12)
    {g : UnitAddCircle → ℝ} (hg : BMC g) : BM (fun ω : JointSpace => condInt ρ.value i g ω.1) :=
  BM.of_position (condInt_bounded hρ i hg)

/-- **Chain rule** `Ent(ρ) = ∑_i E[Ent(p_i(·|x_{<i}))]`, the expectation being taken under the joint law
(`p_i = conditionalDensity ρ i`, a version of the conditional density by `condExp_position`). -/
theorem entropy_eq_sum_expect (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) :
    entropy ρ = ∑ i : Fin 12, ∫ ω, conditionalEntropy ρ.value i ω.1 ∂jointLaw ρ := by
  unfold entropy
  rw [entropy_chain_rule_full hρ ρ.mass]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_jointLaw_position ρ (conditional_entropy_bounded hρ i)]


theorem BM.finsetSum {ι : Type*} (T : Finset ι) {F : ι → JointSpace → ℝ}
    (h : ∀ a ∈ T, BM (F a)) : BM (fun w => ∑ a ∈ T, F a w) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using BM.const 0
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact BM.add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- One coordinate of the integrated Lemma 5.16 bound, with Jensen under the joint law:
`2E[I_B(t_i)] + ψ(E t_i) + (1/40)(E r_2)² + (2/15)(E r_3)² + (27/40)∑_{n∈s}(E r_{n+4})²/(n+4) ≤ E[Ent p_i]`,
where `E t_i = E cos 2πx_i` and `E r_{i,n} = E cos 2πn x_i` by the tower property. -/
theorem integrate_budget_jointLaw (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value)
    (i : Fin 12) (s : Finset ℕ)
    (hr : ∀ x, condInt ρ.value i (cosFn 1) x ∈ Icc (0 : ℝ) 1)
    (hb : ∀ x,
      2 * binaryCost (condInt ρ.value i (cosFn 1) x) +
      BecknerOnofri.V2.Circle.psi (condInt ρ.value i (cosFn 1) x) +
      (1 / 40) * (condInt ρ.value i (cosFn 2) x) ^ 2 +
      (2 / 15) * (condInt ρ.value i (cosFn 3) x) ^ 2 +
      (27 / 40) * (∑ n ∈ s, (condInt ρ.value i (cosFn (n + 4)) x) ^ 2 / ((n : ℝ) + 4)) ≤
        conditionalEntropy ρ.value i x) :
    2 * (∫ w, binaryCost (condInt ρ.value i (cosFn 1) w.1) ∂jointLaw ρ) +
      BecknerOnofri.V2.Circle.psi (∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ) +
      (1 / 40) * (∫ w, cosFn 2 (w.1 i) ∂jointLaw ρ) ^ 2 +
      (2 / 15) * (∫ w, cosFn 3 (w.1 i) ∂jointLaw ρ) ^ 2 +
      (27 / 40) * (∑ n ∈ s, (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4)) ≤
        ∫ w, conditionalEntropy ρ.value i w.1 ∂jointLaw ρ := by
  let ψ := BecknerOnofri.V2.Circle.psi
  let T : JointSpace → ℝ := fun w => condInt ρ.value i (cosFn 1) w.1
  let R : ℕ → JointSpace → ℝ := fun n w => condInt ρ.value i (cosFn n) w.1
  have hT : BM T := BM.condInt ρ hρ i (bmc_cosFn 1)
  have hR (n : ℕ) : BM (R n) := BM.condInt ρ hρ i (bmc_cosFn n)
  have hTr : ∀ w, T w ∈ Icc (0 : ℝ) 1 := fun w => hr w.1
  have hψc : ContinuousOn ψ (Icc (0 : ℝ) 1) := BecknerOnofri.V2.Circle.psi_continuousOn
  have hψv : ConvexOn ℝ (Icc (0 : ℝ) 1) ψ := BecknerOnofri.V2.Circle.psi_convexOn
  have hB : BM (fun w => binaryCost (T w)) := by
    obtain ⟨hm, C, hC⟩ := conditional_binaryCost_bounded hρ i
    exact BM.of_position ⟨hm, C, hC⟩
  have hP : BM (fun w => ψ (T w)) := by
    obtain ⟨hm, C, hC⟩ := bounded_comp_Icc' (condInt_bounded hρ i (bmc_cosFn 1)) hr ψ hψc
    exact BM.of_position ⟨hm, C, hC⟩
  have hQ (n : ℕ) : BM (fun w => (R n w) ^ 2) := by
    simpa only [pow_two] using (hR n).mul (hR n)
  have hsum : BM (fun w => ∑ n ∈ s, (R (n + 4) w) ^ 2 / ((n : ℝ) + 4)) :=
    BM.finsetSum s fun n _ => by
      simpa only [div_eq_mul_inv] using (hQ (n + 4)).mul (BM.const ((n : ℝ) + 4)⁻¹)
  have hH : BM (fun w => conditionalEntropy ρ.value i w.1) :=
    BM.of_position (conditional_entropy_bounded hρ i)
  have hmult (w : JointSpace) :
      2 * binaryCost (T w) + ψ (T w) + (1 / 40) * (R 2 w) ^ 2 + (2 / 15) * (R 3 w) ^ 2 +
        (27 / 40) * (∑ n ∈ s, (R (n + 4) w) ^ 2 / ((n : ℝ) + 4)) ≤
          conditionalEntropy ρ.value i w.1 := hb w.1
  have c1 : BM (fun w => 2 * binaryCost (T w)) := (BM.const 2).mul hB
  have c3 : BM (fun w => (1 / 40) * (R 2 w) ^ 2) := (BM.const _).mul (hQ 2)
  have c4 : BM (fun w => (2 / 15) * (R 3 w) ^ 2) := (BM.const _).mul (hQ 3)
  have c5 : BM (fun w => (27 / 40) * (∑ n ∈ s, (R (n + 4) w) ^ 2 / ((n : ℝ) + 4))) :=
    (BM.const _).mul hsum
  have I1 : BM (fun w => 2 * binaryCost (T w) + ψ (T w)) := c1.add hP
  have I2 : BM (fun w => 2 * binaryCost (T w) + ψ (T w) + (1 / 40) * (R 2 w) ^ 2) := I1.add c3
  have I3 : BM (fun w => 2 * binaryCost (T w) + ψ (T w) + (1 / 40) * (R 2 w) ^ 2 +
      (2 / 15) * (R 3 w) ^ 2) := I2.add c4
  have I4 : BM (fun w => 2 * binaryCost (T w) + ψ (T w) + (1 / 40) * (R 2 w) ^ 2 +
      (2 / 15) * (R 3 w) ^ 2 + (27 / 40) * (∑ n ∈ s, (R (n + 4) w) ^ 2 / ((n : ℝ) + 4))) :=
    I3.add c5
  have h := integral_mono (I4.integrable (jointLaw ρ)) (hH.integrable (jointLaw ρ)) hmult
  rw [integral_add (I3.integrable _) (c5.integrable _), integral_add (I2.integrable _) (c4.integrable _),
    integral_add (I1.integrable _) (c3.integrable _), integral_add (c1.integrable _) (hP.integrable _)] at h
  simp only [integral_const_mul] at h
  have hterm (n : ℕ) : Integrable (fun w => (R (n + 4) w) ^ 2 / ((n : ℝ) + 4)) (jointLaw ρ) :=
    ((hQ (n + 4)).integrable _).div_const _
  rw [integral_finsetSum s (fun n _ => hterm n)] at h
  simp only [integral_div] at h
  -- Jensen under the joint law
  have hsq (n : ℕ) : (∫ w, R n w ∂jointLaw ρ) ^ 2 ≤ ∫ w, (R n w) ^ 2 ∂jointLaw ρ := by
    have hv : ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t : ℝ => t ^ 2) :=
      (Even.convexOn_pow ⟨1, rfl⟩).subset (subset_univ _) (convex_Icc _ _)
    exact jensen_jointLaw ρ (hR n) (fun w => abs_le.mp (conditional_moment_abs_le_one hρ i n w.1))
      (fun t => t ^ 2) (continuous_pow 2).continuousOn hv
  have hψj : ψ (∫ w, T w ∂jointLaw ρ) ≤ ∫ w, ψ (T w) ∂jointLaw ρ :=
    jensen_jointLaw ρ hT hTr ψ hψc hψv
  have hE (n : ℕ) : (∫ w, R n w ∂jointLaw ρ) = ∫ w, cosFn n (w.1 i) ∂jointLaw ρ :=
    integral_condInt ρ hρ i (bmc_cosFn n)
  have hE1 : (∫ w, T w ∂jointLaw ρ) = ∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ := hE 1
  rw [hE1] at hψj
  have hsq' (n : ℕ) : (∫ w, cosFn n (w.1 i) ∂jointLaw ρ) ^ 2 ≤ ∫ w, (R n w) ^ 2 ∂jointLaw ρ := by
    rw [← hE n]; exact hsq n
  have ht : (∑ n ∈ s, (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4)) ≤
      ∑ n ∈ s, (∫ w, (R (n + 4) w) ^ 2 ∂jointLaw ρ) / ((n : ℝ) + 4) := by
    apply Finset.sum_le_sum
    intro n _
    exact div_le_div_of_nonneg_right (hsq' (n + 4)) (by positivity)
  have h2 := hsq' 2
  have h3 := hsq' 3
  linarith


open scoped ContDiff in
/-- **`eq:section5-channel-continuous-entropy`**, with every expectation taken under the joint law:
`Ent(ρ) ≥ 2 ∑_i E[I_B(t_i)] + ∑_i ψ(E cos 2πx_i) + ∑_i [ (E cos 4πx_i)²/40 + 2(E cos 6πx_i)²/15
+ (27/40) ∑_{n≥4} (E cos 2πn x_i)²/n ]`; here `E cos 2πn x_i = Re ρ̂(n e_i)`. -/
theorem continuous_entropy_jointLaw (ρ : ProbabilityDensity 12) {V : (Fin 12 → ℝ) → ℝ}
    (hV : ContDiffOn ℝ ∞ V (cosineCube 12))
    (h1 : ∀ v ∈ cosineCube 12, ∀ i : Fin 12, 0 ≤ cosinePartial i V v)
    (hrep : ∀ x, ρ.value x = Real.exp (V (cosineVector x))) (hs : SmoothOnTorus ρ.value) :
    (∀ i : Fin 12, Summable (fun n : ℕ =>
      (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4))) ∧
    2 * (∑ i : Fin 12, ∫ w, binaryCost (condInt ρ.value i (cosFn 1) w.1) ∂jointLaw ρ) +
      (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi (∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ)) +
      (1 / 40) * (∑ i : Fin 12, (∫ w, cosFn 2 (w.1 i) ∂jointLaw ρ) ^ 2) +
      (2 / 15) * (∑ i : Fin 12, (∫ w, cosFn 3 (w.1 i) ∂jointLaw ρ) ^ 2) +
      (27 / 40) * (∑ i : Fin 12, ∑' n : ℕ,
        (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4)) ≤ entropy ρ := by
  have hf : PositiveBounded ρ.value := rep_positiveBounded hV.continuousOn hrep
  have hstats (i : Fin 12) (x : Torus 12) := conditional_explicit hV h1 hrep hs i x
  have hpoint (s : Finset ℕ) (i : Fin 12) (x : Torus 12) :
      2 * binaryCost (condInt ρ.value i (cosFn 1) x) +
      BecknerOnofri.V2.Circle.psi (condInt ρ.value i (cosFn 1) x) +
      (1 / 40) * (condInt ρ.value i (cosFn 2) x) ^ 2 +
      (2 / 15) * (condInt ρ.value i (cosFn 3) x) ^ 2 +
      (27 / 40) * (∑ n ∈ s, (condInt ρ.value i (cosFn (n + 4)) x) ^ 2 / ((n : ℝ) + 4)) ≤
        conditionalEntropy ρ.value i x := by
    obtain ⟨_, _, hsm, hmain⟩ := hstats i x
    have hsum := Summable.sum_le_tsum s (fun n _ => by positivity) hsm
    have : ∀ n : ℕ, condInt ρ.value i (cosFn n) x = conditionalCosineMoment ρ.value i n x :=
      fun n => rfl
    simp only [this]
    linarith
  let q := fun (i : Fin 12) (n : ℕ) => (∫ w, cosFn (n + 4) (w.1 i) ∂jointLaw ρ) ^ 2 / ((n : ℝ) + 4)
  let A := 2 * (∑ i : Fin 12, ∫ w, binaryCost (condInt ρ.value i (cosFn 1) w.1) ∂jointLaw ρ) +
      (∑ i : Fin 12, BecknerOnofri.V2.Circle.psi (∫ w, cosFn 1 (w.1 i) ∂jointLaw ρ)) +
      (1 / 40) * (∑ i : Fin 12, (∫ w, cosFn 2 (w.1 i) ∂jointLaw ρ) ^ 2) +
      (2 / 15) * (∑ i : Fin 12, (∫ w, cosFn 3 (w.1 i) ∂jointLaw ρ) ^ 2)
  have hfinite (s : Finset ℕ) : A + (27 / 40) * (∑ n ∈ s, ∑ i : Fin 12, q i n) ≤ entropy ρ := by
    rw [Finset.sum_comm]
    have hi (i : Fin 12) := integrate_budget_jointLaw ρ hf i s
      (fun x => ⟨(hstats i x).1, (hstats i x).2.1.le⟩) (hpoint s i)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    rw [entropy_eq_sum_expect ρ hf]
    dsimp only [A, q]
    linarith
  have hq (i : Fin 12) (n : ℕ) : 0 ≤ q i n := by dsimp [q]; positivity
  obtain ⟨hs', hb⟩ := nonneg_budget_limit (fun n => ∑ i : Fin 12, q i n)
    (fun n => Finset.sum_nonneg (fun i _ => hq i n)) A (entropy ρ) (27 / 40) (by norm_num) hfinite
  have hi (i : Fin 12) : Summable (q i) :=
    hs'.of_nonneg_of_le (hq i) (fun n => Finset.single_le_sum (fun j _ => hq j n) (Finset.mem_univ i))
  refine ⟨hi, ?_⟩
  rw [Summable.tsum_finsetSum (fun i _ => hi i)] at hb
  exact hb

end BecknerOnofri.V2.Reaudit.SpinChannel
