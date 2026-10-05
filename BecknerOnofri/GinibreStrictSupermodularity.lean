module

public import BecknerOnofri.CosineCoefficientLattice

@[expose] public section

/-! Strict coefficient comparison from the genuine positive covariance term.
These are actual Banach-space derivatives of the full summable potential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.GinibreCovariance
open ContinuousGibbs

theorem cosineSeries_add_smul {d : ℕ} (a p : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hp : ∀ k,0≤p k) (has : Summable a) (hps : Summable p) (t : ℝ) :
    cosineSeries a id+t • cosineSeries p id=cosineSeries (fun k => a k+t*p k) id := by
  have hsa := cosineSeries_summable a id ha has
  have hsp := cosineSeries_summable p id hp hps
  unfold cosineSeries
  rw [← hsp.tsum_const_smul t,← hsa.tsum_add (hsp.const_smul t)]
  apply tsum_congr
  intro k
  simp only [add_smul,mul_smul]

theorem cosineSeries_hasSum_map {d : ℕ} (L : Space d →L[ℝ] ℝ)
    (a : Frequency d → ℝ) (ha : ∀ k,0≤a k) (has : Summable a) :
    HasSum (fun k => a k*L (cosine k)) (L (cosineSeries a id)) := by
  convert! ((cosineSeries_summable a id ha has).hasSum.map L.toAddMonoidHom L.continuous) using 1
  funext k
  change a k*L (cosine k)=L (a k • cosine k)
  rw [map_smul,smul_eq_mul]

theorem cosineSeries_hessian_direction_pos {d : ℕ} (a p : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hp : ∀ k,0≤p k) (has : Summable a) (hps : Summable p)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (hps' : 0<p s) (had : 0<a (r-s)) :
    0<logPartitionHessian (cosineSeries a id) (cosineSeries p id) (cosine r) := by
  rw [logPartitionHessian_symmetric]
  have hsum := cosineSeries_hasSum_map (logPartitionHessian (cosineSeries a id) (cosine r)) p hp hps
  rw [← hsum.tsum_eq]
  apply hsum.summable.tsum_pos
  · intro k
    exact mul_nonneg (hp k) (cosineSeries_covariance_nonneg a id ha has r k)
  · exact mul_pos hps' (cosineSeries_covariance_pos a id ha has r s hr hs hrs (r-s) rfl had)

/-- A positive coefficient increment strictly increases the indicated actual
cosine expectation when the base has the positive difference-frequency mode. -/
theorem cosineSeries_expectation_strict_increment {d : ℕ} (a p : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hp : ∀ k,0≤p k) (has : Summable a) (hps : Summable p)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (hps' : 0<p s) (had : 0<a (r-s)) :
    weightedMean (cosineSeries a id) (cosine r)<
      weightedMean (cosineSeries (fun k => a k+p k) id) (cosine r) := by
  let q := cosineSeries a id
  let v := cosineSeries p id
  have hD (t : ℝ) := cosine_expectation_hasDerivAt q v r t
  have hc : Continuous (fun t : ℝ => weightedMean (q+t • v) (cosine r)) :=
    continuous_iff_continuousAt.mpr (fun t => (hD t).continuousAt)
  have hmono : StrictMonoOn (fun t : ℝ => weightedMean (q+t • v) (cosine r)) (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hD t).deriv]
    change 0<logPartitionHessian (cosineSeries a id+t • cosineSeries p id) (cosineSeries p id) (cosine r)
    rw [cosineSeries_add_smul a p ha hp has hps]
    apply cosineSeries_hessian_direction_pos (fun k => a k+t*p k) p
      (fun k => add_nonneg (ha k) (mul_nonneg ht.1.le (hp k))) hp
      (has.add (hps.mul_left t)) hps r s hr hs hrs hps'
    exact add_pos_of_pos_of_nonneg had (mul_nonneg ht.1.le (hp _))
  have hh := hmono (by simp : (0:ℝ)∈Icc 0 1) (by simp : (1:ℝ)∈Icc 0 1) (by norm_num)
  simpa only [zero_smul,add_zero,q,v,cosineSeries_add_smul a p ha hp has hps,one_mul] using hh

theorem cosineSeries_logPartition_increment_strict {d : ℕ} (a b p : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hab : ∀ k,a k≤b k) (hp : ∀ k,0≤p k)
    (has : Summable a) (hbs : Summable b) (hps : Summable p)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (hpr : 0<p r) (hbs' : a s<b s) (had : 0<a (r-s)) :
    logPartitionReal (cosineSeries b id)-logPartitionReal (cosineSeries a id)<
      logPartitionReal (cosineSeries (fun k => b k+p k) id)-
        logPartitionReal (cosineSeries (fun k => a k+p k) id) := by
  let qa := cosineSeries a id
  let qb := cosineSeries b id
  let v := cosineSeries p id
  have hb (k) : 0≤b k := (ha k).trans (hab k)
  have hD (t : ℝ) : HasDerivAt (fun s : ℝ => logPartitionReal (qb+s • v)-logPartitionReal (qa+s • v))
      (weightedMean (qb+t • v) v-weightedMean (qa+t • v) v) t := by
    convert! (logPartition_line_hasDerivAt qb v t).sub (logPartition_line_hasDerivAt qa v t) using 1
  have hc : Continuous (fun t : ℝ => logPartitionReal (qb+t • v)-logPartitionReal (qa+t • v)) :=
    continuous_iff_continuousAt.mpr (fun t => (hD t).continuousAt)
  have hmono : StrictMonoOn (fun t : ℝ => logPartitionReal (qb+t • v)-logPartitionReal (qa+t • v))
      (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    rw [(hD t).deriv]
    let L := weightedMean (qb+t • v)-weightedMean (qa+t • v)
    change 0<L v
    have hsum := cosineSeries_hasSum_map L p hp hps
    rw [show v=cosineSeries p id from rfl,← hsum.tsum_eq]
    have hm (k : Frequency d) : weightedMean (qa+t • v) (cosine k)≤weightedMean (qb+t • v) (cosine k) := by
      dsimp only [qa,qb,v]
      rw [cosineSeries_add_smul a p ha hp has hps,cosineSeries_add_smul b p hb hp hbs hps]
      exact cosineSeries_expectation_mono (fun j => a j+t*p j) (fun j => b j+t*p j) id
        (fun j => add_nonneg (ha j) (mul_nonneg ht.1.le (hp j)))
        (fun j => add_le_add (hab j) le_rfl) (has.add (hps.mul_left t)) (hbs.add (hps.mul_left t)) k
    have hstrict : weightedMean (qa+t • v) (cosine r)<weightedMean (qb+t • v) (cosine r) := by
      have hq (k) : 0≤b k-a k := sub_nonneg.mpr (hab k)
      have hh := cosineSeries_expectation_strict_increment (fun k => a k+t*p k) (fun k => b k-a k)
        (fun k => add_nonneg (ha k) (mul_nonneg ht.1.le (hp k))) hq
        (has.add (hps.mul_left t)) (hbs.sub has) r s hr hs hrs (sub_pos.mpr hbs')
        (add_pos_of_pos_of_nonneg had (mul_nonneg ht.1.le (hp _)))
      have he : (fun k => a k+t*p k+(b k-a k))=(fun k => b k+t*p k) := by funext k; ring
      rw [he] at hh
      simpa only [qa,qb,v,cosineSeries_add_smul a p ha hp has hps,
        cosineSeries_add_smul b p hb hp hbs hps] using hh
    apply hsum.summable.tsum_pos
    · intro k
      change 0≤p k*(weightedMean (qb+t • v) (cosine k)-weightedMean (qa+t • v) (cosine k))
      exact mul_nonneg (hp k) (sub_nonneg.mpr (hm k))
    · change 0<p r*(weightedMean (qb+t • v) (cosine r)-weightedMean (qa+t • v) (cosine r))
      exact mul_pos hpr (sub_pos.mpr hstrict)
  have hh := hmono (by simp : (0:ℝ)∈Icc 0 1) (by simp : (1:ℝ)∈Icc 0 1) (by norm_num)
  simpa only [zero_smul,add_zero,qa,qb,v,cosineSeries_add_smul a p ha hp has hps,
    cosineSeries_add_smul b p hb hp hbs hps,one_mul] using hh

/-- Strict supermodularity in two genuinely crossing coefficients, provided
the common positive support contains their difference frequency. -/
theorem cosineSeries_logPartition_strict_supermodular {d : ℕ} (a b : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hb : ∀ k,0≤b k) (has : Summable a) (hbs : Summable b)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (hpr : b r<a r) (hqs : a s<b s) (had : 0<min (a (r-s)) (b (r-s))) :
    logPartitionReal (cosineSeries a id)+logPartitionReal (cosineSeries b id)<
      logPartitionReal (cosineSeries (fun k => max (a k) (b k)) id)+
        logPartitionReal (cosineSeries (fun k => min (a k) (b k)) id) := by
  let c := fun k => min (a k) (b k)
  have hc (k) : 0≤c k := le_min (ha k) (hb k)
  have hcs : Summable c := has.of_nonneg_of_le hc (fun k => min_le_left _ _)
  have hleft : (fun k => c k+(a k-c k))=a := by funext k; ring
  have hright : (fun k => b k+(a k-c k))=(fun k => max (a k) (b k)) := by
    funext k
    dsimp only [c]
    linarith [max_add_min (a k) (b k)]
  have hp (k) : 0≤a k-c k := sub_nonneg.mpr (min_le_left _ _)
  have hpr' : 0<a r-c r := by dsimp only [c]; rw [min_eq_right hpr.le]; exact sub_pos.mpr hpr
  have hqs' : c s<b s := by dsimp only [c]; rw [min_eq_left hqs.le]; exact hqs
  have hh := cosineSeries_logPartition_increment_strict c b (fun k => a k-c k) hc
    (fun k => min_le_right _ _) hp hcs hbs (has.sub hcs) r s hr hs hrs hpr' hqs' had
  rw [hleft,hright] at hh
  linarith

open CosineCoefficientLattice in
/-- The strict inequality is for the original actual Sobolev functional. -/
theorem functional_strict_supermodular {d : ℕ} {a b : Frequency d → ℝ}
    (ha : Domain a) (hb : Domain b) (A : ℝ)
    (r s : Frequency d) (hr : r≠0) (hs : s≠0) (hrs : r≠s)
    (hpr : b r<a r) (hqs : a s<b s) (had : 0<min (a (r-s)) (b (r-s))) :
    Legacy.BecknerOnofri.SubcriticalAttainment.functional A (toPotential a)+
        Legacy.BecknerOnofri.SubcriticalAttainment.functional A (toPotential b)<
      Legacy.BecknerOnofri.SubcriticalAttainment.functional A (toPotential (fun k => max (a k) (b k)))+
        Legacy.BecknerOnofri.SubcriticalAttainment.functional A (toPotential (fun k => min (a k) (b k))) := by
  rw [toPotential_functional ha,toPotential_functional hb,
    toPotential_functional (ha.max hb),toPotential_functional (ha.min hb)]
  have hh := cosineSeries_logPartition_strict_supermodular a b ha.nonneg hb.nonneg ha.summable hb.summable
    r s hr hs hrs hpr hqs had
  have he := congrArg (fun x : ℝ => A*x) (energy_lattice ha hb)
  simp only [mul_add] at he
  linarith only [hh,he]

#print axioms cosineSeries_hessian_direction_pos
#print axioms cosineSeries_expectation_strict_increment
#print axioms cosineSeries_logPartition_strict_supermodular
#print axioms functional_strict_supermodular
end BecknerOnofri.HighDim.GinibreCovariance
