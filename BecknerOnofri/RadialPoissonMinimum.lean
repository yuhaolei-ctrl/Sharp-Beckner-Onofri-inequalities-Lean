import BecknerOnofri.RadialPoissonImages

/-! Exact diagonal minima for the finite five-symbol Poisson image set. -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialPoissonImages

def imageCenter (k : Frequency 12) : ℝ :=
  max 0 (min (1/2) (-(∑i,(k i:ℝ))/12))
def imageMinimum (k : Frequency 12) : ℝ := radius (imageCenter k) k

theorem imageCenter_nonneg (k : Frequency 12) : 0 ≤ imageCenter k := le_max_left _ _
theorem imageCenter_le_half (k : Frequency 12) : imageCenter k≤1/2 :=
  max_le (by norm_num) (min_le_left _ _)

theorem radius_expansion (y : ℝ) (k : Frequency 12) :
    radius y k=(∑i,(k i:ℝ)^2)+2*y*(∑i,(k i:ℝ))+12*y^2 := by
  unfold radius
  simp_rw [add_sq,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  ring

/-- Clipping the unconstrained quadratic minimizer gives the exact minimum. -/
theorem imageMinimum_le (k : Frequency 12) {y : ℝ} (hy : 0≤y) (hy' : y≤1/2) :
    imageMinimum k≤radius y k := by
  unfold imageMinimum
  rw [radius_expansion,radius_expansion]
  let a : ℝ := ∑i,(k i:ℝ)
  change (∑i,(k i:ℝ)^2)+2*imageCenter k*a+12*(imageCenter k)^2≤
    (∑i,(k i:ℝ)^2)+2*y*a+12*y^2
  have hc : imageCenter k=max 0 (min (1/2) (-a/12)) := rfl
  by_cases ha : 0≤a
  · have he : imageCenter k=0 := by
      rw [hc,max_eq_left]
      exact (min_le_right _ _).trans (by linarith)
    rw [he]
    nlinarith [mul_nonneg hy ha,sq_nonneg y]
  · by_cases hb : a≤ -6
    · have he : imageCenter k=1/2 := by
        rw [hc,min_eq_left (by linarith),max_eq_right (by norm_num)]
      rw [he]
      nlinarith [sq_nonneg (y-1/2),mul_nonneg (show 0≤ -a-6 by linarith)
        (show 0≤1/2-y by linarith)]
    · have he : imageCenter k= -a/12 := by
        rw [hc,min_eq_right (by linarith),max_eq_right (by linarith)]
      rw [he]
      nlinarith [sq_nonneg (y+a/12)]

/-- Every nonzero integer image remains uniformly separated from this diagonal segment. -/
theorem radius_nonzero_lower {d : ℕ} (k : Frequency d) (hk : k≠0) {y : ℝ}
    (hy : 0≤y) (hy' : y≤1/2) : (1:ℝ)/4≤radius y k := by
  have hex : ∃i,k i≠0 := by
    by_contra h
    push Not at h
    exact hk (funext h)
  obtain ⟨i,hi⟩:=hex
  have hs : (1:ℝ)/4≤((k i:ℝ)+y)^2 := by
    have hi' : k i≤ -1 ∨ 1≤k i := by omega
    rcases hi' with h | h
    · have h' : (k i:ℝ)≤ -1 := by exact_mod_cast h
      nlinarith [sq_nonneg ((k i:ℝ)+y+1/2)]
    · have h' : (1:ℝ)≤k i := by exact_mod_cast h
      nlinarith [sq_nonneg ((k i:ℝ)+y-1)]
  exact hs.trans (Finset.single_le_sum (fun j hj=>sq_nonneg ((k j:ℝ)+y)) (Finset.mem_univ i))

theorem imageMinimum_pos (k : Frequency 12) (hk : k≠0) : 0 < imageMinimum k :=
  lt_of_lt_of_le (by norm_num) (radius_nonzero_lower k hk (imageCenter_nonneg k) (imageCenter_le_half k))

/-- Actual per-image estimate at the exact clipped minimum. -/
theorem image_E1_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    (k : Frequency 12) (hk : k≠0) :
    RadialE1.E1 (p*radius y k)≤Real.exp (-p*imageMinimum k)/(p*imageMinimum k) := by
  have hmin:=imageMinimum_pos k hk
  exact (RadialE1.antitone (mul_pos hp hmin)
    (mul_le_mul_of_nonneg_left (imageMinimum_le k hy hy') hp.le)).trans
    (by simpa only [neg_mul] using RadialE1.exponential_bound (mul_pos hp hmin))

/-- This is the finite term in the source's explicit choice of J₁₂. -/
def finiteImageBound (p : ℝ) : ℝ :=
  ∑k∈CubeLatticeTail.cube 12 2,Real.exp (-p*imageMinimum k)/(p*imageMinimum k)

theorem finite_E1_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    (∑k∈CubeLatticeTail.cube 12 2,RadialE1.E1 (p*radius y k))≤finiteImageBound p := by
  apply Finset.sum_le_sum
  intro k hk
  exact image_E1_le hp hy hy' k ((CubeLatticeTail.mem_cube k).mp hk).1

#print axioms imageMinimum_le
#print axioms finite_E1_le
end BecknerOnofri.HighDim.RadialPoissonImages
