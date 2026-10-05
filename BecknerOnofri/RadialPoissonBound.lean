import BecknerOnofri.RadialPoissonMinimum

/-! Complete analytic upper bound for all nonzero diagonal Poisson images. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Classical Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialPoissonImages
open IterationOmittedTail

abbrev NonzeroImage (d : ℕ) := {k : Frequency d // k≠0}

theorem nonzero_E1_summable {d : ℕ} {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    Summable (fun k : NonzeroImage d=>RadialE1.E1 (p*radius y k.val)) := by
  apply (((gaussianVector_summable (d:=d) hp hy hy').div_const (p/4)).subtype
    (fun k : Frequency d=>k≠0)).of_nonneg_of_le
  · intro k
    have hr:=radius_nonzero_lower k.val k.property hy hy'
    apply RadialE1.nonneg
    positivity
  · intro k
    have hr:=radius_nonzero_lower k.val k.property hy hy'
    have hb : 0<p/4 := by positivity
    have hpr : p/4≤p*radius y k.val := by nlinarith
    exact (RadialE1.exponential_bound (hb.trans_le hpr)).trans (by
      dsimp only [Function.comp_apply]
      rw [gaussianVector_eq,neg_mul]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hb hpr)

private def finiteNonzero : Finset (NonzeroImage 12) :=
  (CubeLatticeTail.cube 12 2).subtype (fun k=>k≠0)

private def complementEquiv :
    ↥((finiteNonzero : Set (NonzeroImage 12))ᶜ) ≃ OmittedFrequency (CubeLatticeTail.cube 12 2) where
  toFun k := ⟨k.val.val,k.val.property,fun hk=>k.property (by simpa only [finiteNonzero,Finset.mem_coe,Finset.mem_subtype] using hk)⟩
  invFun k := ⟨⟨k.val,k.property.1⟩,fun hk=>k.property.2 (by simpa only [finiteNonzero,Finset.mem_coe,Finset.mem_subtype] using hk)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact separation into the finite five-symbol cube and the actual omitted image series. -/
theorem nonzero_E1_split {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    (∑'k : NonzeroImage 12,RadialE1.E1 (p*radius y k.val))=
      (∑k∈CubeLatticeTail.cube 12 2,RadialE1.E1 (p*radius y k))+
      ∑'k : OmittedFrequency (CubeLatticeTail.cube 12 2),RadialE1.E1 (p*radius y k.val) := by
  rw [← (nonzero_E1_summable (d:=12) hp hy hy').sum_add_tsum_compl (s:=finiteNonzero)]
  have hfinite : (∑k∈finiteNonzero,RadialE1.E1 (p*radius y k.val))=
      ∑k∈CubeLatticeTail.cube 12 2,RadialE1.E1 (p*radius y k) :=
    Finset.sum_subtype_of_mem (s:=CubeLatticeTail.cube 12 2)
      (fun k=>RadialE1.E1 (p*radius y k)) (fun k hk=>((CubeLatticeTail.mem_cube k).mp hk).1)
  rw [hfinite]
  congr 1
  exact complementEquiv.tsum_eq (fun k=>RadialE1.E1 (p*radius y k.val))

/-- The source's full finite-image-plus-tail estimate, for the actual nonzero image sum. -/
theorem nonzero_E1_bound {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    (∑'k : NonzeroImage 12,RadialE1.E1 (p*radius y k.val))≤
      finiteImageBound p+imageTailBound p 12 := by
  rw [nonzero_E1_split hp hy hy']
  exact add_le_add (finite_E1_le hp hy hy') (omitted_E1_tsum_le hp hy hy' 11)

/-- The explicit choice J₁₂ in the source, with c=π⁶/Γ(6). -/
def J12 : ℝ := (Real.pi^6/Real.Gamma 6)*
  (finiteImageBound (Real.pi^2)+imageTailBound (Real.pi^2) 12)

theorem diagonal_nonzero_images_le_J12 {y : ℝ} (hy : 0≤y) (hy' : y≤1/2) :
    (Real.pi^6/Real.Gamma 6)*
      (∑'k : NonzeroImage 12,RadialE1.E1 (Real.pi^2*radius y k.val))≤J12 := by
  exact mul_le_mul_of_nonneg_left (nonzero_E1_bound (sq_pos_of_pos Real.pi_pos) hy hy')
    (div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<6)).le)

#print axioms diagonal_nonzero_images_le_J12
end BecknerOnofri.HighDim.RadialPoissonImages
