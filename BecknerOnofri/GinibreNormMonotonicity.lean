module

public import BecknerOnofri.GinibreSeries
public import BecknerOnofri.ContinuousFirstShell

@[expose] public section

/-! Partition and actual Gibbs L² norm are coefficientwise monotone on
nonnegative cosine potentials, including uniformly convergent summable series. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs ContinuousFirstShell

theorem cosine_mean_nonneg {d : ℕ} (k : Frequency d) : 0≤mean d (cosine k) := by
  have he : mean d (cosine k)=(coefficient k (ContinuousMap.const (Torus d) 1)).re := by
    rw [coefficient_integral]
    simp only [ContinuousMap.const_apply,Complex.ofReal_one,mul_one]
    have hre : (∫ x, UnitAddTorus.mFourier (-k) x ∂torusMeasure d).re =
        ∫ x, (UnitAddTorus.mFourier (-k) x).re ∂torusMeasure d := by
      convert! (integral_re (𝕜 := ℂ) (μ := torusMeasure d)
        ((UnitAddTorus.mFourier (-k)).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).symm using 1
    rw [hre]
    simp only [UnitAddTorus.mFourier_neg,Complex.conj_re,mean_apply,cosine_apply]
  rw [he,coefficient_const]
  split_ifs <;> norm_num

theorem cosine_expectation_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (r : Frequency d) :
    0≤weightedMean (cosinePotential a k) (cosine r) := by
  have hh := cosine_expectation_mono (fun _ : ι => 0) a k (fun _ => le_rfl) ha r
  have hz : cosinePotential (fun _ : ι => (0:ℝ)) k=0 := by simp [cosinePotential]
  rw [hz,weightedMean_zero] at hh
  exact (cosine_mean_nonneg r).trans hh

theorem logPartition_line_hasDerivAt {d : ℕ} (q v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logPartitionReal (q+s • v)) (weightedMean (q+t • v) v) t := by
  apply HasFDerivAt.comp_hasDerivAt t (f := fun s : ℝ => q+s • v) (l := @logPartitionReal d)
    (f' := v) (l' := weightedMean (q+t • v))
  · convert! hasFDerivAt_logPartitionReal (q+t • v) using 1
  · convert! ((hasDerivAt_id t).smul_const v).const_add q using 1 <;> simp

private theorem endpoint_mono {F D : ℝ → ℝ} (hD : ∀ t,HasDerivAt F (D t) t)
    (hpos : ∀ t,0≤t → t≤1 → 0≤D t) : F 0≤F 1 := by
  have hcont : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hD t).continuousAt)
  have hmono : MonotoneOn F (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
      (fun t _ => (hD t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [interior_Icc] at ht
    rw [(hD t).deriv]
    exact hpos t ht.1.le ht.2.le
  exact hmono (by simp) (by simp) (by norm_num)

theorem cosinePotential_smul {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ℝ) (a : ι → ℝ) (k : ι → Frequency d) :
    c • cosinePotential a k=cosinePotential (fun i => c*a i) k := by
  simp only [cosinePotential,Finset.smul_sum,smul_smul]

private theorem line_endpoint {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) :
    cosinePotential a k+(1:ℝ) • cosinePotential (fun i => b i-a i) k=cosinePotential b k := by
  rw [cosinePotential_line]
  congr 1
  funext i
  ring

theorem cosine_partition_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i) :
    partition (cosinePotential a k)≤partition (cosinePotential b k) := by
  let q := cosinePotential a k
  let v := cosinePotential (fun i => b i-a i) k
  have hh := endpoint_mono (logPartition_line_hasDerivAt q v) (fun t ht _ => ?_)
  · rw [show q+(0:ℝ) • v=q by simp,show q+(1:ℝ) • v=cosinePotential b k from line_endpoint a b k] at hh
    exact (Real.log_le_log_iff (partition_pos q) (partition_pos _)).mp hh
  · change 0≤weightedMean (cosinePotential a k+t • cosinePotential (fun i => b i-a i) k)
      (cosinePotential (fun i => b i-a i) k)
    rw [cosinePotential_line]
    simp only [cosinePotential,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (hab i))
      (cosine_expectation_nonneg (fun i => a i+t*(b i-a i)) k
        (fun i => add_nonneg (ha i) (mul_nonneg ht (sub_nonneg.mpr (hab i)))) (k i))

/-- Logarithm of the square of the actual normalized Gibbs L² norm. -/
def logNormSquared {d : ℕ} (q : Space d) : ℝ :=
  logPartitionReal ((2:ℝ) • q)-2*logPartitionReal q

theorem logNormSquared_line_hasDerivAt {d : ℕ} (q v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => logNormSquared (q+s • v))
      (2*(weightedMean ((2:ℝ) • (q+t • v)) v-weightedMean (q+t • v) v)) t := by
  have h := (logPartition_line_hasDerivAt ((2:ℝ) • q) ((2:ℝ) • v) t).sub
    ((logPartition_line_hasDerivAt q v t).const_mul 2)
  have he (s : ℝ) : (2:ℝ) • (q+s • v)=(2:ℝ) • q+s • ((2:ℝ) • v) := by module
  convert! h using 1
  · funext s
    rw [logNormSquared,he]
    rfl
  · rw [← he,map_smul]
    simp only [smul_eq_mul]
    ring

theorem cosine_logNormSquared_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i) :
    logNormSquared (cosinePotential a k)≤logNormSquared (cosinePotential b k) := by
  let q := cosinePotential a k
  let v := cosinePotential (fun i => b i-a i) k
  have hh := endpoint_mono (logNormSquared_line_hasDerivAt q v) (fun t ht _ => ?_)
  · change logNormSquared (cosinePotential a k+(0:ℝ) • cosinePotential (fun i => b i-a i) k)≤
      logNormSquared (cosinePotential a k+(1:ℝ) • cosinePotential (fun i => b i-a i) k) at hh
    simpa only [zero_smul,add_zero,line_endpoint] using hh
  · apply mul_nonneg (by norm_num)
    apply sub_nonneg.mpr
    change weightedMean (cosinePotential a k+t • cosinePotential (fun i => b i-a i) k)
      (cosinePotential (fun i => b i-a i) k)≤
        weightedMean ((2:ℝ) • (cosinePotential a k+t • cosinePotential (fun i => b i-a i) k))
          (cosinePotential (fun i => b i-a i) k)
    rw [cosinePotential_line,cosinePotential_smul]
    simp only [cosinePotential,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hab i))
    apply cosine_expectation_mono (fun i => a i+t*(b i-a i)) (fun i => 2*(a i+t*(b i-a i))) k
    · intro i
      exact add_nonneg (ha i) (mul_nonneg ht (sub_nonneg.mpr (hab i)))
    · intro i
      have := add_nonneg (ha i) (mul_nonneg ht (sub_nonneg.mpr (hab i)))
      linarith

def gibbsL2Norm {d : ℕ} (q : Space d) : ℝ :=
  Real.sqrt (∫ x, (normalizedGibbs q x)^2 ∂torusMeasure d)

theorem gibbsL2Norm_partition {d : ℕ} (q : Space d) :
    gibbsL2Norm q=Real.sqrt (partition ((2:ℝ) • q)/(partition q)^2) := by
  unfold gibbsL2Norm
  congr 1
  simp only [partition,mean_apply,exponential_apply]
  rw [← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [normalizedGibbs, ContinuousMap.smul_apply, smul_eq_mul, div_pow]
    rw [show (2:ℝ)*q x=q x+q x by ring,Real.exp_add,pow_two])

theorem exp_logNormSquared {d : ℕ} (q : Space d) :
    Real.exp (logNormSquared q)=partition ((2:ℝ) • q)/(partition q)^2 := by
  rw [logNormSquared,Real.exp_sub]
  rw [show (2:ℝ)*logPartitionReal q=logPartitionReal q+logPartitionReal q by ring,Real.exp_add]
  rw [pow_two]
  simp only [logPartitionReal,Real.exp_log (partition_pos q),Real.exp_log (partition_pos ((2:ℝ) • q))]

theorem gibbsL2Norm_logNormSquared {d : ℕ} (q : Space d) :
    gibbsL2Norm q=Real.sqrt (Real.exp (logNormSquared q)) := by
  rw [exp_logNormSquared,gibbsL2Norm_partition]

theorem cosine_gibbsL2Norm_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i) :
    gibbsL2Norm (cosinePotential a k)≤gibbsL2Norm (cosinePotential b k) := by
  rw [gibbsL2Norm_logNormSquared,gibbsL2Norm_logNormSquared]
  exact Real.sqrt_le_sqrt (Real.exp_le_exp.mpr (cosine_logNormSquared_mono a b k ha hab))

theorem partition_continuous {d : ℕ} : Continuous (@partition d) :=
  continuous_iff_continuousAt.mpr (fun q => (partition_analytic q).continuousAt)

theorem logNormSquared_continuous {d : ℕ} : Continuous (@logNormSquared d) := by
  have hc : Continuous (@logPartitionReal d) := continuous_iff_continuousAt.mpr
    (fun q => (hasFDerivAt_logPartitionReal q).continuousAt)
  unfold logNormSquared
  exact (hc.comp ((continuous_const : Continuous (fun _ : Space d => (2:ℝ))).smul continuous_id)).sub
    ((continuous_const : Continuous (fun _ : Space d => (2:ℝ))).mul hc)

theorem gibbsL2Norm_continuous {d : ℕ} : Continuous (@gibbsL2Norm d) := by
  have he : (@gibbsL2Norm d)=(fun q => Real.sqrt (Real.exp (logNormSquared q))) :=
    funext gibbsL2Norm_logNormSquared
  rw [he]
  exact (Real.continuous_exp.comp logNormSquared_continuous).sqrt

theorem gibbsL2Norm_partition_div {d : ℕ} (q : Space d) :
    gibbsL2Norm q=Real.sqrt (partition ((2:ℝ) • q))/partition q := by
  rw [gibbsL2Norm_partition,Real.sqrt_div (partition_pos _).le,
    Real.sqrt_sq (partition_pos q).le]

/-- Coefficientwise partition comparison for an arbitrary summable cosine family. -/
theorem cosineSeries_partition_mono {d : ℕ} {ι : Type*}
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i)
    (has : Summable a) (hbs : Summable b) :
    partition (cosineSeries a k)≤partition (cosineSeries b k) := by
  have hb (i : ι) : 0≤b i := (ha i).trans (hab i)
  have hl := partition_continuous.tendsto (cosineSeries a k)
    |>.comp (cosineSeries_tendsto a k ha has)
  have hr := partition_continuous.tendsto (cosineSeries b k)
    |>.comp (cosineSeries_tendsto b k hb hbs)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun F : Finset ι =>
    cosine_partition_mono (fun i : F => a i) (fun i => b i) (fun i => k i)
      (fun i => ha i) (fun i => hab i)))

/-- The actual normalized Gibbs L² norm increases with each nonnegative cosine coefficient. -/
theorem cosineSeries_gibbsL2Norm_mono {d : ℕ} {ι : Type*}
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hab : ∀ i,a i≤b i)
    (has : Summable a) (hbs : Summable b) :
    gibbsL2Norm (cosineSeries a k)≤gibbsL2Norm (cosineSeries b k) := by
  have hb (i : ι) : 0≤b i := (ha i).trans (hab i)
  have hl := gibbsL2Norm_continuous.tendsto (cosineSeries a k)
    |>.comp (cosineSeries_tendsto a k ha has)
  have hr := gibbsL2Norm_continuous.tendsto (cosineSeries b k)
    |>.comp (cosineSeries_tendsto b k hb hbs)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun F : Finset ι =>
    cosine_gibbsL2Norm_mono (fun i : F => a i) (fun i => b i) (fun i => k i)
      (fun i => ha i) (fun i => hab i)))

#print axioms gibbsL2Norm_partition
#print axioms cosine_partition_mono
#print axioms cosine_gibbsL2Norm_mono
#print axioms cosineSeries_partition_mono
#print axioms cosineSeries_gibbsL2Norm_mono
end BecknerOnofri.HighDim.GinibreCovariance
