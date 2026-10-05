import BecknerOnofri.GinibreNormMonotonicity

/-! The actual log partition is supermodular in nonnegative cosine
coefficients. The infinite-family statement follows from proved uniform
convergence; no interchange of uncontrolled derivatives or sums is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs

theorem cosinePotential_add_smul {d : ℕ} {ι : Type*} [Fintype ι]
    (a p : ι → ℝ) (k : ι → Frequency d) (t : ℝ) :
    cosinePotential a k+t • cosinePotential p k=cosinePotential (fun i => a i+t*p i) k := by
  simp only [cosinePotential,Finset.smul_sum,← Finset.sum_add_distrib,add_smul,smul_smul]

private theorem endpoint_mono {F D : ℝ → ℝ} (hD : ∀ t,HasDerivAt F (D t) t)
    (hpos : ∀ t,0≤t → t≤1 → 0≤D t) : F 0≤F 1 := by
  have hcont : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hD t).continuousAt)
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) 1) hcont.continuousOn
    (fun t _ => (hD t).differentiableAt.differentiableWithinAt) ?_ (by simp) (by simp) (by norm_num)
  intro t ht
  rw [interior_Icc] at ht
  rw [(hD t).deriv]
  exact hpos t ht.1.le ht.2.le

/-- A nonnegative coefficient increment has larger log-partition gain at a
larger nonnegative base point. -/
theorem cosine_logPartition_increment_mono {d : ℕ} {ι : Type*} [Fintype ι]
    (a b p : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i)
    (hab : ∀ i,a i≤b i) (hp : ∀ i,0≤p i) :
    logPartitionReal (cosinePotential b k)-logPartitionReal (cosinePotential a k)≤
      logPartitionReal (cosinePotential (fun i => b i+p i) k)-
        logPartitionReal (cosinePotential (fun i => a i+p i) k) := by
  let qa := cosinePotential a k
  let qb := cosinePotential b k
  let v := cosinePotential p k
  have hD (t : ℝ) := (logPartition_line_hasDerivAt qb v t).sub
    (logPartition_line_hasDerivAt qa v t)
  have hh := endpoint_mono hD (fun t ht _ => ?_)
  · simpa only [Pi.sub_apply,zero_mul,zero_smul,add_zero,qa,qb,v,cosinePotential_add_smul,one_mul] using hh
  · apply sub_nonneg.mpr
    change weightedMean (cosinePotential a k+t • cosinePotential p k) (cosinePotential p k)≤
      weightedMean (cosinePotential b k+t • cosinePotential p k) (cosinePotential p k)
    rw [cosinePotential_add_smul,cosinePotential_add_smul]
    simp only [cosinePotential,map_sum,map_smul,smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hp i)
    exact cosine_expectation_mono (fun j => a j+t*p j) (fun j => b j+t*p j) k
      (fun j => add_nonneg (ha j) (mul_nonneg ht (hp j)))
      (fun j => add_le_add (hab j) le_rfl) (k i)

theorem cosine_logPartition_supermodular {d : ℕ} {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) :
    logPartitionReal (cosinePotential a k)+logPartitionReal (cosinePotential b k)≤
      logPartitionReal (cosinePotential (fun i => max (a i) (b i)) k)+
        logPartitionReal (cosinePotential (fun i => min (a i) (b i)) k) := by
  have hh := cosine_logPartition_increment_mono (fun i => min (a i) (b i)) b
    (fun i => a i-min (a i) (b i)) k (fun i => le_min (ha i) (hb i))
    (fun i => min_le_right _ _) (fun i => sub_nonneg.mpr (min_le_left _ _))
  have hleft : (fun i => min (a i) (b i)+(a i-min (a i) (b i)))=a := by funext i; ring
  have hright : (fun i => b i+(a i-min (a i) (b i)))=(fun i => max (a i) (b i)) := by
    funext i
    linarith [max_add_min (a i) (b i)]
  rw [hleft,hright] at hh
  linarith

theorem logPartition_continuous {d : ℕ} : Continuous (@logPartitionReal d) :=
  continuous_iff_continuousAt.mpr (fun q => (hasFDerivAt_logPartitionReal q).continuousAt)

theorem cosineSeries_logPartition_supermodular {d : ℕ} {ι : Type*}
    (a b : ι → ℝ) (k : ι → Frequency d) (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i)
    (has : Summable a) (hbs : Summable b) :
    logPartitionReal (cosineSeries a k)+logPartitionReal (cosineSeries b k)≤
      logPartitionReal (cosineSeries (fun i => max (a i) (b i)) k)+
        logPartitionReal (cosineSeries (fun i => min (a i) (b i)) k) := by
  have hmin (i) : 0≤min (a i) (b i) := le_min (ha i) (hb i)
  have hmax (i) : 0≤max (a i) (b i) := (ha i).trans (le_max_left _ _)
  have hsmin : Summable (fun i => min (a i) (b i)) :=
    has.of_nonneg_of_le hmin (fun i => min_le_left _ _)
  have hsmax : Summable (fun i => max (a i) (b i)) :=
    (has.add hbs).of_nonneg_of_le hmax (fun i => max_le
      (le_add_of_nonneg_right (hb i)) (le_add_of_nonneg_left (ha i)))
  have hl := ((logPartition_continuous.tendsto _).comp (cosineSeries_tendsto a k ha has)).add
    ((logPartition_continuous.tendsto _).comp (cosineSeries_tendsto b k hb hbs))
  have hr := ((logPartition_continuous.tendsto _).comp (cosineSeries_tendsto _ k hmax hsmax)).add
    ((logPartition_continuous.tendsto _).comp (cosineSeries_tendsto _ k hmin hsmin))
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall (fun F : Finset ι =>
    cosine_logPartition_supermodular (fun i : F => a i) (fun i => b i) (fun i => k i)
      (fun i => ha i) (fun i => hb i)))

#print axioms cosine_logPartition_supermodular
#print axioms cosineSeries_logPartition_supermodular
end BecknerOnofri.HighDim.GinibreCovariance
