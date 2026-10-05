module

public import BecknerOnofri.RadialPoissonGaussian
public import BecknerOnofri.CubeTailBound

@[expose] public section

/-! Actual uniform Poisson image remainder outside the five-point coordinate cube. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.RadialPoissonImages
open RadialPoissonGaussian IterationOmittedTail

/-- Squared distance of an integer image from a point on the diagonal. -/
def radius {d : ℕ} (y : ℝ) (k : Frequency d) : ℝ := ∑i,((k i:ℝ)+y)^2

def gaussianVector {d : ℕ} (p y : ℝ) (k : Frequency d) : ℝ := ∏i,gaussian p y (k i)

def gaussianBound (p : ℝ) : ℝ := 1+2*Real.exp (-p/4)/(1-Real.exp (-2*p))

theorem gaussianVector_nonneg {d : ℕ} (p y : ℝ) (k : Frequency d) : 0≤gaussianVector p y k :=
  Finset.prod_nonneg (fun i hi=>(Real.exp_pos _).le)

theorem gaussianVector_eq {d : ℕ} (p y : ℝ) (k : Frequency d) :
    gaussianVector p y k=Real.exp (-p*radius y k) := by
  rw [radius,Finset.mul_sum,Real.exp_sum]
  rfl

theorem finite_gaussianVector_bound {d : ℕ} {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    (B : Finset (Frequency d)) : (∑k∈B,gaussianVector p y k)≤gaussianBound p^d := by
  let D : Fin d→Finset ℤ := fun i=>B.image (fun k=>k i)
  have hsub : B⊆Fintype.piFinset D := by
    intro k hk
    simp only [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.mpr ⟨k,hk,rfl⟩
  calc
    _ ≤ ∑k∈Fintype.piFinset D,gaussianVector p y k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk hk'=>gaussianVector_nonneg _ _ _)
    _ = ∏i,∑n∈D i,gaussian p y n := (Finset.prod_univ_sum D (fun _ n=>gaussian p y n)).symm
    _ ≤ ∏_i : Fin d,gaussianBound p := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun n hn=>(Real.exp_pos _).le)
      · intro i hi
        exact ((gaussian_summable hp hy hy').sum_le_tsum (D i) (fun n hn=>(Real.exp_pos _).le)).trans
          (gaussian_tsum_le hp hy hy')
    _ = _ := by simp

theorem gaussianVector_summable {d : ℕ} {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    Summable (gaussianVector p y : Frequency d→ℝ) :=
  summable_of_sum_le (gaussianVector_nonneg _ _) (finite_gaussianVector_bound hp hy hy')

theorem gaussianVector_tsum_le {d : ℕ} {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) :
    (∑'k : Frequency d,gaussianVector p y k)≤gaussianBound p^d :=
  (gaussianVector_summable hp hy hy').tsum_le_of_sum_le (finite_gaussianVector_bound hp hy hy')

theorem radius_decode {m N : ℕ} (y : ℝ) (c : CubeLatticeTail.CylinderCode m) :
    radius y (CubeLatticeTail.decode N c)=
      (((if c.2.1 then ((c.2.2.1+N:ℕ):ℤ) else -((c.2.2.1+N:ℕ):ℤ)):ℝ)+y)^2+
        radius y c.2.2.2 := by
  unfold radius
  rw [Fin.sum_univ_succAbove _ c.1]
  simp only [CubeLatticeTail.decode,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  split_ifs <;> simp

def cylinderMajorant (p y : ℝ) (m : ℕ) (v : ℕ×Frequency m) : ℝ :=
  majorant p 3 v.1*gaussianVector p y v.2

theorem cylinderMajorant_nonneg (p y : ℝ) (m : ℕ) (v : ℕ×Frequency m) :
    0≤cylinderMajorant p y m v :=
  mul_nonneg (by unfold majorant; positivity) (gaussianVector_nonneg _ _ _)

theorem cylinderMajorant_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    Summable (cylinderMajorant p y m) :=
  (majorant_summable (N:=3) hp (by omega)).mul_of_nonneg
    (gaussianVector_summable (d:=m) hp hy hy') (by intro n; unfold majorant; positivity)
    (gaussianVector_nonneg _ _)

theorem cylinderMajorant_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    (∑'v,cylinderMajorant p y m v) ≤
      Real.exp (-25*p/4)/(1-Real.exp (-6*p))*gaussianBound p^m := by
  have hs:=cylinderMajorant_summable hp hy hy' m
  have hinner (n : ℕ) : Summable (fun k=>cylinderMajorant p y m (n,k)) := by
    change Summable (fun k : Frequency m=>majorant p 3 n*gaussianVector p y k)
    exact (gaussianVector_summable (d:=m) hp hy hy').mul_left _
  rw [hs.tsum_prod' hinner]
  simp only [cylinderMajorant,tsum_mul_left,tsum_mul_right]
  have he : (∑'n,majorant p 3 n)=Real.exp (-25*p/4)/(1-Real.exp (-6*p)) := by
    rw [majorant_tsum hp (by omega : 0<3)]
    norm_num only [Nat.cast_ofNat]
    congr 2 <;> ring
  rw [he]
  apply mul_le_mul_of_nonneg_left (gaussianVector_tsum_le (d:=m) hp hy hy')
  rw [← he]
  exact tsum_nonneg (fun n=>by unfold majorant; positivity)

theorem decoded_gaussian_bound {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {m : ℕ} (c : CubeLatticeTail.CylinderCode m) :
    gaussianVector p y (CubeLatticeTail.decode 3 c) ≤ cylinderMajorant p y m c.2.2 := by
  rw [gaussianVector_eq,radius_decode,mul_add,Real.exp_add]
  rw [cylinderMajorant,gaussianVector_eq]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  cases hc : c.2.1
  · simpa [gaussian,hc] using
      (gaussian_tail_bound (N:=3) hp hy hy' (by omega) c.2.2.1).2
  · simpa [gaussian,hc] using
      (gaussian_tail_bound (N:=3) hp hy hy' (by omega) c.2.2.1).1

def imageTailBound (p : ℝ) (d : ℕ) : ℝ :=
  (2*d:ℝ)*gaussianBound p^(d-1)*Real.exp (-25*p/4)/
    ((25*p/4)*(1-Real.exp (-6*p)))

theorem radius_nonneg {d : ℕ} (y : ℝ) (k : Frequency d) : 0≤radius y k :=
  Finset.sum_nonneg (fun i hi=>sq_nonneg _)

theorem radius_decode_lower {y : ℝ} (hy : 0≤y) (hy' : y≤1/2)
    {m : ℕ} (c : CubeLatticeTail.CylinderCode m) :
    (25:ℝ)/4≤radius y (CubeLatticeTail.decode 3 c) := by
  rw [radius_decode]
  have hs:=square_bound c.2.2.1 (N:=3) (by omega) hy hy'
  have hr:=radius_nonneg y c.2.2.2
  have hn : (0:ℝ)≤c.2.2.1 := Nat.cast_nonneg _
  cases hc : c.2.1 <;> simp only [hc,Bool.false_eq_true,if_false,ite_true]
  · push_cast at *
    nlinarith [hs.2]
  · push_cast at *
    nlinarith [hs.1]

def codeMajorant (p y : ℝ) (m : ℕ) (c : CubeLatticeTail.CylinderCode m) : ℝ :=
  cylinderMajorant p y m c.2.2/(25*p/4)

theorem codeMajorant_nonneg {p : ℝ} (hp : 0<p) (y : ℝ) (m : ℕ)
    (c : CubeLatticeTail.CylinderCode m) : 0≤codeMajorant p y m c :=
  div_nonneg (cylinderMajorant_nonneg _ _ _ _) (by positivity)

theorem decoded_E1_bound {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2)
    {m : ℕ} (c : CubeLatticeTail.CylinderCode m) :
    RadialE1.E1 (p*radius y (CubeLatticeTail.decode 3 c))≤codeMajorant p y m c := by
  have hr := radius_decode_lower hy hy' c
  have hb : 0<25*p/4 := by positivity
  have hpr : 25*p/4≤p*radius y (CubeLatticeTail.decode 3 c) := by nlinarith
  calc
    _ ≤ Real.exp (- (p*radius y (CubeLatticeTail.decode 3 c)))/
        (p*radius y (CubeLatticeTail.decode 3 c)) := RadialE1.exponential_bound (hb.trans_le hpr)
    _ ≤ gaussianVector p y (CubeLatticeTail.decode 3 c)/(25*p/4) := by
      rw [gaussianVector_eq,neg_mul]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hb hpr
    _ ≤ _ := div_le_div_of_nonneg_right (decoded_gaussian_bound hp hy hy' c) hb.le

theorem codeMajorant_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    Summable (codeMajorant p y m) := by
  have hc := (cylinderMajorant_summable hp hy hy' m).div_const (25*p/4)
  have hb : Summable (fun c : Bool×(ℕ×Frequency m)=>cylinderMajorant p y m c.2/(25*p/4)) :=
    (summable_prod_of_nonneg (fun c=>codeMajorant_nonneg hp y m (0,c))).mpr
      ⟨fun b=>hc,(hasSum_fintype _).summable⟩
  exact (summable_prod_of_nonneg (codeMajorant_nonneg hp y m)).mpr
    ⟨fun i=>hb,(hasSum_fintype _).summable⟩

theorem codeMajorant_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    (∑'c,codeMajorant p y m c) ≤ imageTailBound p (m+1) := by
  have hc := (cylinderMajorant_summable hp hy hy' m).div_const (25*p/4)
  have hb : Summable (fun c : Bool×(ℕ×Frequency m)=>cylinderMajorant p y m c.2/(25*p/4)) :=
    (summable_prod_of_nonneg (fun c=>codeMajorant_nonneg hp y m (0,c))).mpr
      ⟨fun b=>hc,(hasSum_fintype _).summable⟩
  rw [(codeMajorant_summable hp hy hy' m).tsum_prod' (fun i=>hb)]
  have he : (∑'i : Fin (m+1),∑'c : Bool×(ℕ×Frequency m),codeMajorant p y m (i,c))=
      2*(m+1:ℝ)*(∑'v,cylinderMajorant p y m v)/(25*p/4) := by
    simp only [codeMajorant]
    rw [hb.tsum_prod' (fun b=>hc)]
    simp [tsum_fintype,tsum_div_const,mul_comm,mul_assoc]
    <;> ring
  rw [he]
  have h:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (cylinderMajorant_tsum_le hp hy hy' m) (by positivity : 0≤2*(m+1:ℝ)))
    (by positivity : 0≤25*p/4)
  convert! h using 1
  unfold imageTailBound
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
  ring

theorem omitted_radius_lower {y : ℝ} (hy : 0≤y) (hy' : y≤1/2)
    {m : ℕ} (k : OmittedFrequency (CubeLatticeTail.cube (m+1) 2)) : (25:ℝ)/4≤radius y k.val := by
  rw [← CubeLatticeTail.decode_encode k]
  exact radius_decode_lower hy hy' _

/-- The genuine omitted Poisson image series is summable. -/
theorem omitted_E1_summable {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    Summable (fun k : OmittedFrequency (CubeLatticeTail.cube (m+1) 2)=>RadialE1.E1 (p*radius y k.val)) := by
  apply ((codeMajorant_summable hp hy hy' m).comp_injective
    (CubeLatticeTail.encode_injective (m:=m) (R:=2))).of_nonneg_of_le
  · intro k
    apply RadialE1.nonneg
    have hr:=omitted_radius_lower hy hy' k
    positivity
  · intro k
    rw [← CubeLatticeTail.decode_encode k]
    exact decoded_E1_bound hp hy hy' _

/-- Exact analytic diagonal image remainder, with the source's Gaussian constants. -/
theorem omitted_E1_tsum_le {p y : ℝ} (hp : 0<p) (hy : 0≤y) (hy' : y≤1/2) (m : ℕ) :
    (∑'k : OmittedFrequency (CubeLatticeTail.cube (m+1) 2),RadialE1.E1 (p*radius y k.val)) ≤
      imageTailBound p (m+1) := by
  refine (Summable.tsum_le_tsum_of_inj CubeLatticeTail.encode CubeLatticeTail.encode_injective
    (fun c hc=>codeMajorant_nonneg hp y m c) (fun k=>?_) (omitted_E1_summable hp hy hy' m)
    (codeMajorant_summable hp hy hy' m)).trans (codeMajorant_tsum_le hp hy hy' m)
  rw [← CubeLatticeTail.decode_encode k]
  exact decoded_E1_bound hp hy hy' _

/-- Dimension-twelve specialization of the infinite remainder in the source formula for J₁₂. -/
theorem omitted_E1_twelve {y : ℝ} (hy : 0≤y) (hy' : y≤1/2) :
    (∑'k : OmittedFrequency (CubeLatticeTail.cube 12 2),RadialE1.E1 (Real.pi^2*radius y k.val)) ≤
      24*gaussianBound (Real.pi^2)^11*Real.exp (-(25*Real.pi^2/4))/
        ((25*Real.pi^2/4)*(1-Real.exp (-6*Real.pi^2))) := by
  convert! omitted_E1_tsum_le (p:=Real.pi^2) (sq_pos_of_pos Real.pi_pos) hy hy' 11 using 1
  norm_num only [imageTailBound,Nat.cast_ofNat,Nat.reduceAdd,Nat.reduceSub]
  ring

#print axioms omitted_E1_twelve
end BecknerOnofri.HighDim.RadialPoissonImages
