module

public import BecknerOnofri.V2.Reaudit.SpinChannel.Tower
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

@[expose] public section

/-!
# Conditional expectations under the joint law

The sub-σ-algebras `σ(x_{<i})`, `σ(σ_{<i})`, `σ(x_{<i}, σ_{<i})` of the joint space and the three
conditional-expectation statements of the printed proof:

* `E[g(x_i) | x_{<i}] = ∫ g p_i(· | x_{<i})` (so `r_{i,n}`, `t_i` are the conditional cosine moments);
* `E[σ_i | x_{<i}, σ_{<i}] = t_i(x_{<i})` (conditional independence of the earlier spins and `σ_i`);
* `E[σ_i | σ_{<i}] = E[t_i | σ_{<i}]`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option warn.classDefReducibility false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer
open BecknerOnofri.HighDim.ConditionalEntropy

theorem measurable_posMask (k : ℕ) : Measurable (posMask k) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j.val < k
  · simpa [posMask, h] using measurable_pi_apply j
  · simp [posMask, h]

theorem measurable_spinMask (k : ℕ) : Measurable (spinMask k) := measurable_of_finite _

/-- The map `ω ↦ (x_{<k}, σ_{<k})`. -/
def Yk (k : ℕ) (ω : JointSpace) : JointSpace := (posMask k ω.1, spinMask k ω.2)

theorem measurable_Yk (k : ℕ) : Measurable (Yk k) :=
  ((measurable_posMask k).comp measurable_fst).prodMk ((measurable_spinMask k).comp measurable_snd)

/-- `σ(x_{<k})`. -/
def sigmaPos (k : ℕ) : MeasurableSpace JointSpace :=
  MeasurableSpace.comap (fun ω : JointSpace => posMask k ω.1) inferInstance

/-- `σ(σ_{<k})`. -/
def sigmaSpin (k : ℕ) : MeasurableSpace JointSpace :=
  MeasurableSpace.comap (fun ω : JointSpace => spinMask k ω.2) inferInstance

/-- `σ(x_{<k}, σ_{<k})`. -/
def sigmaBoth (k : ℕ) : MeasurableSpace JointSpace :=
  MeasurableSpace.comap (Yk k) inferInstance

theorem sigmaPos_le (k : ℕ) : sigmaPos k ≤ (inferInstance : MeasurableSpace JointSpace) :=
  (measurable_posMask k |>.comp measurable_fst).comap_le

theorem sigmaSpin_le (k : ℕ) : sigmaSpin k ≤ (inferInstance : MeasurableSpace JointSpace) :=
  (measurable_spinMask k |>.comp measurable_snd).comap_le

theorem sigmaBoth_le (k : ℕ) : sigmaBoth k ≤ (inferInstance : MeasurableSpace JointSpace) :=
  (measurable_Yk k).comap_le

theorem sigmaSpin_le_sigmaBoth (k : ℕ) : sigmaSpin k ≤ sigmaBoth k := by
  intro s hs
  obtain ⟨B, hB, rfl⟩ := hs
  refine ⟨Prod.snd ⁻¹' B, measurable_snd hB, ?_⟩
  rfl

theorem sigmaPos_le_sigmaBoth (k : ℕ) : sigmaPos k ≤ sigmaBoth k := by
  intro s hs
  obtain ⟨B, hB, rfl⟩ := hs
  refine ⟨Prod.fst ⁻¹' B, measurable_fst hB, ?_⟩
  rfl

/-- Characterization of a conditional expectation given a measurable map `Y`: a bounded measurable
function of `Y` with the right integrals over the sets `Y ⁻¹' B`. -/
theorem condExp_comap_ae_eq (ρ : ProbabilityDensity 12) {β : Type*} [MeasurableSpace β]
    (Y : JointSpace → β) (hY : Measurable Y) {f : JointSpace → ℝ} (hf : BM f) {g : β → ℝ}
    (hg : Measurable g) (hgb : ∃ B, ∀ b, ‖g b‖ ≤ B)
    (h : ∀ B : Set β, MeasurableSet B →
      ∫ ω in Y ⁻¹' B, g (Y ω) ∂jointLaw ρ = ∫ ω in Y ⁻¹' B, f ω ∂jointLaw ρ) :
    condExp (MeasurableSpace.comap Y inferInstance) (jointLaw ρ) f =ᵐ[jointLaw ρ] fun ω => g (Y ω) := by
  have hm : MeasurableSpace.comap Y inferInstance ≤ (inferInstance : MeasurableSpace JointSpace) :=
    hY.comap_le
  have : IsFiniteMeasure ((jointLaw ρ).trim hm) := isFiniteMeasure_trim hm
  obtain ⟨B0, hB0⟩ := hgb
  have hgY : Measurable (fun ω => g (Y ω)) := hg.comp hY
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm (hf.integrable _) ?_ ?_ ?_).symm
  · intro s _ _
    exact (Integrable.of_bound (C := B0) hgY.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hB0 (Y ω))).integrableOn
  · intro s hs _
    obtain ⟨B, hB, rfl⟩ := hs
    exact h B hB
  · have : Measurable[MeasurableSpace.comap Y inferInstance] (fun ω => g (Y ω)) :=
      hg.comp (comap_measurable Y)
    exact this.stronglyMeasurable.aestronglyMeasurable

theorem BM.spinCoord (i : Fin 12) : BM (spinCoord i) := by
  unfold SpinChannel.spinCoord
  exact BM.of_spin (fun s : Spins => if s i then (1 : ℝ) else -1)

/-- `E_P[Θ(x_{<k}, σ_{<k})] = ∫ ρ(x) ∑_a P(σ_{<k} = a | x) Θ(x_{<k}, a) dm`. -/
theorem integral_jointLaw_Yk (ρ : ProbabilityDensity 12) (k : ℕ) {Θ : JointSpace → ℝ} (hΘ : BM Θ) :
    ∫ ω, Θ (Yk k ω) ∂jointLaw ρ =
      ∫ x, ρ.value x * ∑ a ∈ Pat k, lik k a x * Θ (posMask k x, a) ∂torusMeasure 12 := by
  have hBM : BM (fun ω => Θ (Yk k ω)) := by
    obtain ⟨hm, B, hB⟩ := hΘ
    exact ⟨hm.comp (measurable_Yk k), B, fun ω => hB _⟩
  rw [integral_jointLaw ρ (hBM.integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  exact sum_spinWeight_mask_one k x (fun a => Θ (posMask k x, a))

/-- The same with one more factor `σ_i`, `k = i`. -/
theorem integral_jointLaw_Yk_spin (ρ : ProbabilityDensity 12) (i : Fin 12) {Θ : JointSpace → ℝ}
    (hΘ : BM Θ) :
    ∫ ω, Θ (Yk i.val ω) * spinCoord i ω ∂jointLaw ρ =
      ∫ x, ρ.value x * (torusCosines x i *
        ∑ a ∈ Pat i.val, lik i.val a x * Θ (posMask i.val x, a)) ∂torusMeasure 12 := by
  have hBM : BM (fun ω => Θ (Yk i.val ω) * spinCoord i ω) := by
    refine BM.mul ?_ ?_
    · obtain ⟨hm, B, hB⟩ := hΘ
      exact ⟨hm.comp (measurable_Yk _), B, fun ω => hB _⟩
    · exact BM.spinCoord i
  rw [integral_jointLaw ρ (hBM.integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  have := sum_spinWeight_mask_spin i x (fun a => Θ (posMask i.val x, a))
  simpa [Yk, spinCoord] using this


/-- The cosine test function `z ↦ cos(2π n z)`. -/
def cosFn (n : ℕ) (z : UnitAddCircle) : ℝ := (fourier (n : ℤ) z).re

theorem bmc_cosFn (n : ℕ) : BMC (cosFn n) := by
  refine ⟨(Complex.continuous_re.comp (map_continuous (fourier (n : ℤ)))).measurable, 1, fun z => ?_⟩
  calc ‖cosFn n z‖ = |(fourier (n : ℤ) z).re| := Real.norm_eq_abs _
    _ ≤ ‖fourier (n : ℤ) z‖ := Complex.abs_re_le_norm _
    _ = 1 := by simp [fourier_apply]

theorem condInt_posMask (f : Torus 12 → ℝ) (i : Fin 12) (g : UnitAddCircle → ℝ) (x : Torus 12) :
    condInt f i g (posMask i.val x) = condInt f i g x :=
  condInt_prefix_congr f i g fun j hj => by simp [posMask, hj]

/-- The indicator `1_B(posMask_k x)` as a bounded measurable function of `x`. -/
theorem boundedMeasurable_indicator_posMask (k : ℕ) {B : Set (Torus 12)} (hB : MeasurableSet B) :
    BoundedMeasurable (fun x : Torus 12 => (B.indicator (fun _ => (1 : ℝ)) (posMask k x))) := by
  refine ⟨(measurable_const.indicator hB).comp (measurable_posMask k), 1, fun x => ?_⟩
  by_cases h : posMask k x ∈ B <;> simp [h]

/-- **`conditionalDensity` is the conditional density.**  For every bounded measurable test
function `g` of the circle variable, `E[g(x_i) | x_{<i}] = ∫ g(z) p_i(z | x_{<i}) dz` almost surely
under the joint law, where `p_i = conditionalDensity ρ i`.  In particular `r_{i,n}` and `t_i` of the
printed proof are the conditional cosine moments. -/
theorem condExp_position (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12)
    {g : UnitAddCircle → ℝ} (hg : BMC g) :
    condExp (sigmaPos i.val) (jointLaw ρ) (fun ω => g (ω.1 i)) =ᵐ[jointLaw ρ]
      fun ω => condInt ρ.value i g ω.1 := by
  have hbd := condInt_bounded hρ i hg
  obtain ⟨hmeas, Bc, hBc⟩ := hbd
  have key := condExp_comap_ae_eq ρ (fun ω : JointSpace => posMask i.val ω.1)
    ((measurable_posMask _).comp measurable_fst) (f := fun ω => g (ω.1 i))
    (BM.of_position (hg.coord i)) (g := condInt ρ.value i g) hmeas ⟨Bc, hBc⟩ ?_
  · filter_upwards [key] with ω hω
    rw [sigmaPos]
    rw [hω, condInt_posMask]
  · intro B hB
    have hBm : MeasurableSet ((fun ω : JointSpace => posMask i.val ω.1) ⁻¹' B) :=
      ((measurable_posMask _).comp measurable_fst) hB
    rw [← integral_indicator hBm, ← integral_indicator hBm]
    have e1 : ((fun ω : JointSpace => posMask i.val ω.1) ⁻¹' B).indicator
        (fun ω => condInt ρ.value i g (posMask i.val ω.1)) =
        fun ω => (fun x : Torus 12 => B.indicator (fun _ => (1 : ℝ)) (posMask i.val x) *
          condInt ρ.value i g x) ω.1 := by
      funext ω
      by_cases h : posMask i.val ω.1 ∈ B <;> simp [h, Set.indicator, condInt_posMask]
    have e2 : ((fun ω : JointSpace => posMask i.val ω.1) ⁻¹' B).indicator
        (fun ω => g (ω.1 i)) =
        fun ω => (fun x : Torus 12 => B.indicator (fun _ => (1 : ℝ)) (posMask i.val x) *
          g (x i)) ω.1 := by
      funext ω
      by_cases h : posMask i.val ω.1 ∈ B <;> simp [h, Set.indicator]
    rw [e1, e2]
    have hw := boundedMeasurable_indicator_posMask i.val hB
    rw [integral_jointLaw_position ρ (hw.mul ⟨hmeas, Bc, hBc⟩),
      integral_jointLaw_position ρ (hw.mul (hg.coord i))]
    have := condInt_weighted_tower hρ hw i hg (fun x y hxy => by
      have hmask : posMask i.val x = posMask i.val y := by
        funext j
        by_cases hj : j.val < i.val
        · simp [posMask, hj, hxy j hj]
        · simp [posMask, hj]
      simp only [hmask])
    simpa using this


theorem boundedMeasurable_sum {ι : Type*} (T : Finset ι) {F : ι → Torus 12 → ℝ}
    (h : ∀ a ∈ T, BoundedMeasurable (F a)) : BoundedMeasurable (fun x => ∑ a ∈ T, F a x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using BoundedMeasurable.const (d := 12) 0
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem measurable_torusCosines (j : Fin 12) : Measurable (fun x : Torus 12 => torusCosines x j) := by
  unfold torusCosines
  exact (Complex.continuous_re.comp ((map_continuous (fourier (1 : ℤ))).comp
    (continuous_apply j))).measurable

theorem boundedMeasurable_lik (k : ℕ) (a : Spins) : BoundedMeasurable (lik k a) := by
  refine ⟨?_, 1, fun x => ?_⟩
  · unfold lik
    refine Finset.measurable_prod _ fun j _ => ?_
    unfold bernW
    cases a j
    · exact (measurable_const.sub (measurable_torusCosines j)).div_const 2
    · exact (measurable_const.add (measurable_torusCosines j)).div_const 2
  · rw [Real.norm_eq_abs, abs_of_nonneg (lik_nonneg k a x)]
    exact lik_le_one k a x

/-- `W_B(x) = ∑_a P(σ_{<k} = a | x) 1_B(x_{<k}, a)`: a bounded measurable function of `x_{<k}`. -/
def cylW (k : ℕ) (B : Set JointSpace) (x : Torus 12) : ℝ :=
  ∑ a ∈ Pat k, lik k a x * B.indicator (fun _ => (1 : ℝ)) (posMask k x, a)

theorem boundedMeasurable_cylW (k : ℕ) {B : Set JointSpace} (hB : MeasurableSet B) :
    BoundedMeasurable (cylW k B) := by
  refine boundedMeasurable_sum _ fun a _ => (boundedMeasurable_lik k a).mul ?_
  refine ⟨(measurable_const.indicator hB).comp ((measurable_posMask k).prodMk measurable_const),
    1, fun x => ?_⟩
  by_cases h : (posMask k x, a) ∈ B <;> simp [h]

theorem cylW_depends (k : ℕ) (B : Set JointSpace) {x y : Torus 12}
    (hxy : ∀ j : Fin 12, j.val < k → x j = y j) : cylW k B x = cylW k B y := by
  have hmask : posMask k x = posMask k y := by
    funext j
    by_cases hj : j.val < k
    · simp [posMask, hj, hxy j hj]
    · simp [posMask, hj]
  unfold cylW
  apply Finset.sum_congr rfl
  intro a _
  rw [lik_depends k a hxy, hmask]

/-- **`E[σ_i | x_{<i}, σ_{<i}] = t_i(x_{<i})`**: given the earlier positions the earlier spins are
independent of `σ_i`, and `E[σ_i | x] = cos 2πx_i`, so the posterior mean of the spin is the conditional
cosine moment `t_i = E[cos 2πx_i | x_{<i}]`. -/
theorem condExp_spin_both (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12) :
    condExp (sigmaBoth i.val) (jointLaw ρ) (spinCoord i) =ᵐ[jointLaw ρ]
      fun ω => condInt ρ.value i (cosFn 1) ω.1 := by
  obtain ⟨hmeas, Bc, hBc⟩ := condInt_bounded hρ i (bmc_cosFn 1)
  have hgY : Measurable (fun y : JointSpace => condInt ρ.value i (cosFn 1) y.1) :=
    hmeas.comp measurable_fst
  have key := condExp_comap_ae_eq ρ (Yk i.val) (measurable_Yk _) (f := spinCoord i)
    (BM.spinCoord i) (g := fun y : JointSpace => condInt ρ.value i (cosFn 1) y.1) hgY
    ⟨Bc, fun y => hBc _⟩ ?_
  · filter_upwards [key] with ω hω
    rw [sigmaBoth, hω]
    simp only [Yk]
    exact condInt_posMask ρ.value i _ ω.1
  · intro B hB
    have hBm : MeasurableSet (Yk i.val ⁻¹' B) := measurable_Yk _ hB
    rw [← integral_indicator hBm, ← integral_indicator hBm]
    have hΘ1 : BM (B.indicator (fun y : JointSpace => condInt ρ.value i (cosFn 1) y.1)) := by
      refine ⟨(hgY.indicator hB), Bc, fun y => ?_⟩
      by_cases h : y ∈ B
      · simpa [h] using hBc y.1
      · simp [h]; exact (norm_nonneg _).trans (hBc (y.1))
    have hΘ2 : BM (B.indicator (fun _ : JointSpace => (1 : ℝ))) := by
      refine ⟨measurable_const.indicator hB, 1, fun y => ?_⟩
      by_cases h : y ∈ B <;> simp [h]
    have e1 : (Yk i.val ⁻¹' B).indicator (fun ω => condInt ρ.value i (cosFn 1) (Yk i.val ω).1) =
        fun ω => (B.indicator (fun y : JointSpace => condInt ρ.value i (cosFn 1) y.1)) (Yk i.val ω) := by
      funext ω; by_cases h : Yk i.val ω ∈ B <;> simp [h, Set.indicator]
    have e2 : (Yk i.val ⁻¹' B).indicator (spinCoord i) =
        fun ω => (B.indicator (fun _ : JointSpace => (1 : ℝ))) (Yk i.val ω) * spinCoord i ω := by
      funext ω; by_cases h : Yk i.val ω ∈ B <;> simp [h, Set.indicator]
    rw [e1, e2, integral_jointLaw_Yk ρ i.val hΘ1, integral_jointLaw_Yk_spin ρ i hΘ2]
    have hW := boundedMeasurable_cylW i.val hB
    have hpre : ∀ x y : Torus 12, (∀ j : Fin 12, j.val < i.val → x j = y j) →
        cylW i.val B x = cylW i.val B y := fun x y h => cylW_depends _ _ h
    have tower := condInt_weighted_tower hρ hW i (bmc_cosFn 1) hpre
    have lhs : ∀ x : Torus 12, ρ.value x * ∑ a ∈ Pat i.val, lik i.val a x *
        (B.indicator (fun y : JointSpace => condInt ρ.value i (cosFn 1) y.1)) (posMask i.val x, a) =
        ρ.value x * (cylW i.val B x * condInt ρ.value i (cosFn 1) x) := by
      intro x
      congr 1
      unfold cylW
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : (posMask i.val x, a) ∈ B
      · simp [h, Set.indicator, condInt_posMask]
      · simp [h]
    have rhs : ∀ x : Torus 12, ρ.value x * (torusCosines x i * ∑ a ∈ Pat i.val, lik i.val a x *
        (B.indicator (fun _ : JointSpace => (1 : ℝ))) (posMask i.val x, a)) =
        ρ.value x * (cylW i.val B x * cosFn 1 (x i)) := by
      intro x; simp only [cylW, cosFn, torusCosines, Nat.cast_one]; ring
    simp_rw [lhs, rhs]
    exact tower


/-- **`E[σ_i | σ_{<i}] = E[t_i | σ_{<i}]`** (tower property through `σ(x_{<i}, σ_{<i})`). -/
theorem condExp_spin_prefix_eq (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value)
    (i : Fin 12) :
    condExp (sigmaSpin i.val) (jointLaw ρ) (spinCoord i) =ᵐ[jointLaw ρ]
      condExp (sigmaSpin i.val) (jointLaw ρ) (fun ω => condInt ρ.value i (cosFn 1) ω.1) := by
  have : IsFiniteMeasure ((jointLaw ρ).trim (sigmaBoth_le i.val)) := isFiniteMeasure_trim _
  have h1 := condExp_condExp_of_le (μ := jointLaw ρ) (f := spinCoord i)
    (sigmaSpin_le_sigmaBoth i.val) (sigmaBoth_le i.val)
  have h2 := condExp_congr_ae (m := sigmaSpin i.val) (condExp_spin_both ρ hρ i)
  exact h1.symm.trans h2

/-- The probability `ν_ρ(σ_{<k} = a)`: `∫ ρ P(σ_{<k} = a | x) dm`. -/
def prefixProb (ρ : ProbabilityDensity 12) (k : ℕ) (a : Spins) : ℝ :=
  ∫ x, ρ.value x * lik k a x ∂torusMeasure 12

/-- `∫ ρ P(σ_{<i} = a | x) cos 2πx_i dm`: the numerator of the posterior mean of `σ_i`. -/
def prefixSpinMoment (ρ : ProbabilityDensity 12) (i : Fin 12) (a : Spins) : ℝ :=
  ∫ x, ρ.value x * (lik i.val a x * torusCosines x i) ∂torusMeasure 12

/-- The posterior mean `E[σ_i | σ_{<i} = a]` of the current spin given the earlier spins. -/
def postMean (ρ : ProbabilityDensity 12) (i : Fin 12) (a : Spins) : ℝ :=
  prefixSpinMoment ρ i a / prefixProb ρ i.val a

theorem lik_eq_prefixLikelihood (k : ℕ) (a : Spins) (x : Torus 12) :
    lik k a x = prefixLikelihood k (posSet a) x := by
  unfold lik prefixLikelihood
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : a j = true <;> simp [bernW, posSet, h]

theorem prefixProb_pos (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (k : ℕ) (a : Spins) :
    0 < prefixProb ρ k a := by
  unfold prefixProb
  have := prefix_mass_pos hρ k (posSet a)
  simpa only [lik_eq_prefixLikelihood] using this

theorem integrable_rho_lik (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (k : ℕ) (a : Spins)
    {h : Torus 12 → ℝ} (hh : BoundedMeasurable h) :
    Integrable (fun x => ρ.value x * (lik k a x * h x)) (torusMeasure 12) :=
  (hρ.bounded.mul ((boundedMeasurable_lik k a).mul hh)).integrable

/-- `∫ ρ ∑_a P(σ_{<k} = a | x) φ(a) dm = ∑_a ν_ρ(σ_{<k} = a) φ(a)`. -/
theorem integral_rho_sum_lik (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (k : ℕ)
    (φ : Spins → ℝ) :
    ∫ x, ρ.value x * ∑ a ∈ Pat k, lik k a x * φ a ∂torusMeasure 12 =
      ∑ a ∈ Pat k, prefixProb ρ k a * φ a := by
  have : ∀ x : Torus 12, ρ.value x * ∑ a ∈ Pat k, lik k a x * φ a =
      ∑ a ∈ Pat k, (ρ.value x * lik k a x) * φ a := by
    intro x; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  simp_rw [this]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_mul_const]; rfl
  · intro a _
    have := integrable_rho_lik ρ hρ k a (h := fun _ => 1) (BoundedMeasurable.const 1)
    simpa using this.mul_const (φ a)

theorem integral_rho_cos_sum_lik (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12)
    (φ : Spins → ℝ) :
    ∫ x, ρ.value x * (torusCosines x i * ∑ a ∈ Pat i.val, lik i.val a x * φ a) ∂torusMeasure 12 =
      ∑ a ∈ Pat i.val, prefixSpinMoment ρ i a * φ a := by
  have hc : BoundedMeasurable (fun x : Torus 12 => torusCosines x i) :=
    ⟨measurable_torusCosines i, 1, fun x => by simpa using torusCosines_bound x i⟩
  have : ∀ x : Torus 12, ρ.value x * (torusCosines x i * ∑ a ∈ Pat i.val, lik i.val a x * φ a) =
      ∑ a ∈ Pat i.val, (ρ.value x * (lik i.val a x * torusCosines x i)) * φ a := by
    intro x; rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  simp_rw [this]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_mul_const]; rfl
  · intro a _
    exact (integrable_rho_lik ρ hρ i.val a hc).mul_const (φ a)

theorem postMean_mul (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12) (a : Spins) :
    prefixProb ρ i.val a * postMean ρ i a = prefixSpinMoment ρ i a := by
  unfold postMean
  field_simp [(prefixProb_pos ρ hρ i.val a).ne']

theorem abs_postMean_le (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value) (i : Fin 12) (a : Spins) :
    |postMean ρ i a| ≤ 1 := by
  have hc : BoundedMeasurable (fun x : Torus 12 => torusCosines x i) :=
    ⟨measurable_torusCosines i, 1, fun x => by simpa using torusCosines_bound x i⟩
  have hden := prefixProb_pos ρ hρ i.val a
  have h : |prefixSpinMoment ρ i a| ≤ prefixProb ρ i.val a := by
    unfold prefixSpinMoment prefixProb
    have hi1 : Integrable (fun x => ρ.value x * lik i.val a x) (torusMeasure 12) :=
      (hρ.bounded.mul (boundedMeasurable_lik i.val a)).integrable
    refine (abs_integral_le_integral_abs).trans
      (integral_mono (integrable_rho_lik ρ hρ i.val a hc).abs hi1 ?_)
    intro x
    have h1 := hρ.pos x
    have h2 := lik_nonneg i.val a x
    have h3 := torusCosines_bound x i
    simp only [abs_mul, abs_of_pos h1, abs_of_nonneg h2]
    have h4 : lik i.val a x * |torusCosines x i| ≤ lik i.val a x := by
      have := mul_le_mul_of_nonneg_left h3 h2
      rwa [mul_one] at this
    exact mul_le_mul_of_nonneg_left h4 h1.le
  unfold postMean
  rw [abs_div, abs_of_pos hden, div_le_one hden]
  exact h


/-- **The posterior mean of the current spin**: `E[σ_i | σ_{<i}] = postMean ρ i (σ_{<i})`, an explicit
ratio of integrals against the density. -/
theorem condExp_spin_prefix_explicit (ρ : ProbabilityDensity 12) (hρ : PositiveBounded ρ.value)
    (i : Fin 12) :
    condExp (sigmaSpin i.val) (jointLaw ρ) (spinCoord i) =ᵐ[jointLaw ρ]
      fun ω => postMean ρ i (spinMask i.val ω.2) := by
  classical
  have hpm : Measurable (postMean ρ i) := measurable_of_finite _
  have key := condExp_comap_ae_eq ρ (fun ω : JointSpace => spinMask i.val ω.2)
    ((measurable_spinMask _).comp measurable_snd) (f := spinCoord i) (BM.spinCoord i)
    (g := postMean ρ i) hpm ⟨1, fun a => by simpa using abs_postMean_le ρ hρ i a⟩ ?_
  · exact key
  · intro B hB
    have hBm : MeasurableSet ((fun ω : JointSpace => spinMask i.val ω.2) ⁻¹' B) :=
      ((measurable_spinMask _).comp measurable_snd) hB
    rw [← integral_indicator hBm, ← integral_indicator hBm]
    let Θ1 : JointSpace → ℝ := fun y => if y.2 ∈ B then postMean ρ i y.2 else 0
    let Θ2 : JointSpace → ℝ := fun y => if y.2 ∈ B then 1 else 0
    have hΘ1 : BM Θ1 := by
      have := BM.of_spin (fun a : Spins => if a ∈ B then postMean ρ i a else 0)
      exact this
    have hΘ2 : BM Θ2 := by
      have := BM.of_spin (fun a : Spins => if a ∈ B then (1 : ℝ) else 0)
      exact this
    have e1 : ((fun ω : JointSpace => spinMask i.val ω.2) ⁻¹' B).indicator
        (fun ω => postMean ρ i (spinMask i.val ω.2)) = fun ω => Θ1 (Yk i.val ω) := by
      funext ω; by_cases h : spinMask i.val ω.2 ∈ B <;> simp [h, Θ1, Yk, Set.indicator]
    have e2 : ((fun ω : JointSpace => spinMask i.val ω.2) ⁻¹' B).indicator (spinCoord i) =
        fun ω => Θ2 (Yk i.val ω) * spinCoord i ω := by
      funext ω; by_cases h : spinMask i.val ω.2 ∈ B <;> simp [h, Θ2, Yk, Set.indicator]
    rw [e1, e2, integral_jointLaw_Yk ρ i.val hΘ1, integral_jointLaw_Yk_spin ρ i hΘ2]
    have l1 := integral_rho_sum_lik ρ hρ i.val (fun a => if a ∈ B then postMean ρ i a else 0)
    have l2 := integral_rho_cos_sum_lik ρ hρ i (fun a => if a ∈ B then (1 : ℝ) else 0)
    simp only [Θ1, Θ2]
    rw [l1, l2]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a ∈ B
    · simp [h, postMean_mul ρ hρ i a]
    · simp [h]

end BecknerOnofri.V2.Reaudit.SpinChannel
