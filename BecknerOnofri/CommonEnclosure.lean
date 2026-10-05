module

public import BecknerOnofri.GinibreSeries
public import BecknerOnofri.GibbsNormPerturbation
public import BecknerOnofri.GibbsPerturbation
public import BecknerOnofri.GridGibbsComparison

@[expose] public section

/-! The genuine coefficient-update step for a summable nonnegative cosine
potential, finite retained coefficient upper bounds, and a controlled omitted
mass. All grid quantities are exact finite averages on the flat torus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.CommonEnclosure
open ContinuousGibbs GinibreCovariance GridGibbsComparison GibbsPerturbation

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

def retained (A : Finset ι) (b : ι → ℝ) (i : ι) : ℝ := if i∈A then b i else 0

def omitted (A : Finset ι) (a : ι → ℝ) (i : ι) : ℝ := if i∈A then 0 else a i

theorem retained_summable (A : Finset ι) (b : ι → ℝ) : Summable (retained A b) :=
  summable_of_ne_finset_zero (s := A) (fun i hi => by simp [retained,hi])

theorem omitted_summable (A : Finset ι) (a : ι → ℝ) (ha : ∀ i,0≤a i) (hs : Summable a) :
    Summable (omitted A a) := by
  apply hs.of_nonneg_of_le
  · intro i; unfold omitted; split_ifs; exact le_rfl; exact ha i
  · intro i; unfold omitted; split_ifs <;> simp_all

theorem retained_series (A : Finset ι) (b : ι → ℝ) (k : ι → Frequency d) :
    cosineSeries (retained A b) k=cosinePotential (fun i : A => b i) (fun i => k i) := by
  rw [finitePotential_eq_sum,cosineSeries]
  rw [tsum_eq_sum (s := A) (fun i hi => by simp [retained,hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp [retained,hi]

theorem updated_series (A : Finset ι) (a b : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hab : ∀ i∈A,a i≤b i) :
    cosineSeries (fun i => retained A b i+omitted A a i) k=
      cosinePotential (fun i : A => b i) (fun i => k i)+cosineSeries (omitted A a) k := by
  have hb (i) : 0≤retained A b i := by
    unfold retained
    split_ifs with hi
    · exact (ha i).trans (hab i hi)
    · exact le_rfl
  have ho (i) : 0≤omitted A a i := by unfold omitted; split_ifs; exact le_rfl; exact ha i
  rw [← retained_series A b k]
  simp only [cosineSeries,add_smul]
  exact (cosineSeries_summable _ k hb (retained_summable A b)).tsum_add
    (cosineSeries_summable _ k ho (omitted_summable A a ha hs))

theorem original_le_updated (A : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i,0≤a i) (hab : ∀ i∈A,a i≤b i) (i : ι) :
    a i≤retained A b i+omitted A a i := by
  by_cases hi : i∈A
  · simpa [retained,omitted,hi] using hab i hi
  · simp [retained,omitted,hi]

theorem omitted_potential_bound (A : Finset ι) (a : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (δ : ℝ) (hδ : (∑' i,omitted A a i)≤δ)
    (x : Torus d) : |cosineSeries (omitted A a) k x|≤δ := by
  have ho (i) : 0≤omitted A a i := by unfold omitted; split_ifs; exact le_rfl; exact ha i
  exact (show |cosineSeries (omitted A a) k x|≤‖cosineSeries (omitted A a) k‖ by
    simpa only [Real.norm_eq_abs] using (cosineSeries (omitted A a) k).norm_coe_le_norm x).trans
    ((cosineSeries_norm_le _ k ho (omitted_summable A a ha hs)).trans hδ)

/-- Both improvements in the manuscript's coefficient update hold for the
actual infinite-dimensional Gibbs potential. Retained caps need not be exact. -/
theorem coefficient_updates {N : ℕ} [NeZero N]
    (A : Finset ι) (a b : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hab : ∀ i∈A,a i≤b i)
    (δ : ℝ) (hδ : (∑' i,omitted A a i)≤δ) (r : Frequency d) :
    let v := cosinePotential (fun i : A => b i) (fun i => k i)
    let G := gridExpectation (N := N) v (cosine r)
    weightedMean (cosineSeries a k) (cosine r)≤G+δ ∧
      weightedMean (cosineSeries a k) (cosine r)≤1-(1-G)*Real.exp (-2*δ) := by
  let v := cosinePotential (fun i : A => b i) (fun i => k i)
  let w := cosineSeries (omitted A a) k
  have ho (i) : 0≤omitted A a i := by unfold omitted; split_ifs; exact le_rfl; exact ha i
  have hδ0 : 0≤δ := (tsum_nonneg ho).trans hδ
  have hb (i : A) : 0≤b i := (ha i).trans (hab i i.property)
  have hcomp : weightedMean (cosineSeries a k) (cosine r)≤weightedMean (v+w) (cosine r) := by
    have hh := cosineSeries_expectation_mono a (fun i => retained A b i+omitted A a i) k ha
      (original_le_updated A a b ha hab) hs ((retained_summable A b).add (omitted_summable A a ha hs)) r
    rw [updated_series A a b k ha hs hab] at hh
    exact hh
  have hw : ∀ x, |w x|≤δ := omitted_potential_bound A a k ha hs δ hδ
  have hf (x : Torus d) : |cosine r x|≤1 :=
    (show |cosine r x|≤‖cosine r‖ by simpa only [Real.norm_eq_abs] using (cosine r).norm_coe_le_norm x).trans
      (cosine_norm_le_one r)
  have hgrid := cosine_expectation_le_grid (N := N) (fun i : A => b i) (fun i => k i) hb r
  have hadd := expectation_additive_update v w (cosine r) δ hδ0 hw hf
  have hexp := expectation_exponential_update v w (cosine r) δ hw (fun x => (abs_le.mp (hf x)).2)
  constructor
  · change _≤gridExpectation (N := N) v (cosine r)+δ
    linarith [(abs_le.mp hadd).2]
  · change _≤1-(1-gridExpectation (N := N) v (cosine r))*Real.exp (-2*δ)
    have hm := mul_le_mul_of_nonneg_right hgrid (Real.exp_pos (-2*δ)).le
    linarith

/-- A previous coefficient cap may be intersected with both new bounds. -/
theorem coefficient_min_update {N : ℕ} [NeZero N]
    (A : Finset ι) (a b : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hab : ∀ i∈A,a i≤b i)
    (δ : ℝ) (hδ : (∑' i,omitted A a i)≤δ) (r : Frequency d) (X : ℝ)
    (hX : weightedMean (cosineSeries a k) (cosine r)≤X) :
    let G := gridExpectation (N := N) (cosinePotential (fun i : A => b i) (fun i => k i)) (cosine r)
    weightedMean (cosineSeries a k) (cosine r)≤min X (min (G+δ) (1-(1-G)*Real.exp (-2*δ))) := by
  have hh := coefficient_updates (N := N) A a b k ha hs hab δ hδ r
  exact le_min hX (le_min hh.1 hh.2)

/-- The L² norm update for the same actual infinite potential. -/
theorem norm_update {N : ℕ} [NeZero N]
    (A : Finset ι) (a b : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hab : ∀ i∈A,a i≤b i)
    (δ : ℝ) (hδ : (∑' i,omitted A a i)≤δ) (L : ℝ) (hL : 0<L)
    (hLZ : L≤partition (cosinePotential (fun i : A => b i) (fun i => k i))) :
    let v := cosinePotential (fun i : A => b i) (fun i => k i)
    gibbsL2Norm (cosineSeries a k)≤Real.exp δ*Real.sqrt (gridMean (N := N) (exponential ((2:ℝ) • v)))/L := by
  let v := cosinePotential (fun i : A => b i) (fun i => k i)
  let w := cosineSeries (omitted A a) k
  have ho (i) : 0≤omitted A a i := by unfold omitted; split_ifs; exact le_rfl; exact ha i
  have hb (i : A) : 0≤b i := (ha i).trans (hab i i.property)
  have hb' (i) : 0≤retained A b i := by
    unfold retained
    split_ifs with hi
    · exact (ha i).trans (hab i hi)
    · exact le_rfl
  have hs' := (retained_summable A b).add (omitted_summable A a ha hs)
  have hcomp : gibbsL2Norm (cosineSeries a k)≤gibbsL2Norm (v+w) := by
    have hh := cosineSeries_gibbsL2Norm_mono a (fun i => retained A b i+omitted A a i) k ha
      (original_le_updated A a b ha hab) hs hs'
    rw [updated_series A a b k ha hs hab] at hh
    exact hh
  have hZ : partition v≤partition (v+w) := by
    have hh := cosineSeries_partition_mono (retained A b) (fun i => retained A b i+omitted A a i) k hb'
      (fun i => le_add_of_nonneg_right (ho i)) (retained_summable A b) hs'
    rw [retained_series,updated_series A a b k ha hs hab] at hh
    exact hh
  exact hcomp.trans (gibbsL2Norm_grid_perturbation (N := N) (fun i : A => b i) (fun i => k i) hb
    w δ L (fun x => (abs_le.mp (omitted_potential_bound A a k ha hs δ hδ x)).2) hZ hL hLZ)

/-- A prior norm bound is retained at every update. -/
theorem norm_min_update {N : ℕ} [NeZero N]
    (A : Finset ι) (a b : ι → ℝ) (k : ι → Frequency d)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hab : ∀ i∈A,a i≤b i)
    (δ : ℝ) (hδ : (∑' i,omitted A a i)≤δ) (L : ℝ) (hL : 0<L)
    (hLZ : L≤partition (cosinePotential (fun i : A => b i) (fun i => k i)))
    (M : ℝ) (hM : gibbsL2Norm (cosineSeries a k)≤M) :
    let v := cosinePotential (fun i : A => b i) (fun i => k i)
    gibbsL2Norm (cosineSeries a k)≤min M (Real.exp δ*Real.sqrt (gridMean (N := N) (exponential ((2:ℝ) • v)))/L) :=
  le_min hM (norm_update (N := N) A a b k ha hs hab δ hδ L hL hLZ)

#print axioms norm_update
#print axioms norm_min_update
#print axioms coefficient_updates
#print axioms coefficient_min_update
end BecknerOnofri.HighDim.CommonEnclosure
