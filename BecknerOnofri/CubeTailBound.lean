module

public import BecknerOnofri.CubeCylinderTail
public import BecknerOnofri.LatticeDefinitions

@[expose] public section

/-! The exact coordinate/sign union bound for omitted Euclidean lattice mass. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.CubeLatticeTail
open Legacy.TorusEndpoint.GreenMultiplierSummability IterationOmittedTail

/-- The nonzero integer cube used by the enclosure iteration. -/
def cube (d R : ℕ) : Finset (Frequency d) := RectangleLattice.puncturedBox (fun _=>R)

theorem mem_cube {d R : ℕ} (k : Frequency d) :
    k∈cube d R ↔ k≠0 ∧ ∀i,(k i).natAbs≤R := by
  simp only [cube,RectangleLattice.puncturedBox,Finset.mem_filter,RectangleLattice.box,
    Fintype.mem_piFinset,Finset.mem_Icc]
  have he (i : Fin d) : (-(R:ℤ)≤k i ∧ k i≤R) ↔ (k i).natAbs≤R := by
    rw [← abs_le,← Int.natCast_natAbs]
    exact_mod_cast Iff.rfl
  simp_rw [he]
  exact and_comm

abbrev CylinderCode (m : ℕ) := Fin (m+1) × Bool × (ℕ × (Fin m → ℤ))

def decode {m : ℕ} (N : ℕ) (c : CylinderCode m) : Frequency (m+1) :=
  c.1.insertNth (if c.2.1 then ((c.2.2.1+N:ℕ):ℤ) else -((c.2.2.1+N:ℕ):ℤ)) c.2.2.2

theorem exists_decode {m R : ℕ} (k : OmittedFrequency (cube (m+1) R)) :
    ∃ c : CylinderCode m,decode (R+1) c=k.val := by
  have hk : ∃i,R<(k.val i).natAbs := by
    by_contra h
    push Not at h
    exact k.property.2 ((mem_cube k.val).mpr ⟨k.property.1,h⟩)
  obtain ⟨i,hi⟩ := hk
  let n := (k.val i).natAbs-(R+1)
  have hn : n+(R+1)=(k.val i).natAbs := Nat.sub_add_cancel (by omega)
  have habs : ((n+(R+1):ℕ):ℤ)=|k.val i| := by rw [hn,Int.natCast_natAbs]
  by_cases hsign : 0≤k.val i
  · refine ⟨(i,true,n,i.removeNth k.val),?_⟩
    simp only [decode,ite_true]
    rw [habs,abs_of_nonneg hsign,Fin.insertNth_self_removeNth]
  · refine ⟨(i,false,n,i.removeNth k.val),?_⟩
    simp only [decode,Bool.false_eq_true,if_false]
    rw [habs,abs_of_neg (lt_of_not_ge hsign),neg_neg,Fin.insertNth_self_removeNth]

def encode {m R : ℕ} (k : OmittedFrequency (cube (m+1) R)) : CylinderCode m :=
  Classical.choose (exists_decode k)

theorem decode_encode {m R : ℕ} (k : OmittedFrequency (cube (m+1) R)) :
    decode (R+1) (encode k)=k.val := Classical.choose_spec (exists_decode k)

theorem encode_injective {m R : ℕ} :
    Function.Injective (encode : OmittedFrequency (cube (m+1) R) → CylinderCode m) := by
  intro k l h
  apply Subtype.ext
  rw [← decode_encode k,← decode_encode l,h]

theorem radiusSq_decode {m N : ℕ} (c : CylinderCode m) :
    radiusSq (decode N c)=(((c.2.2.1+N:ℕ):ℝ))^2+radiusSq c.2.2.2 := by
  unfold radiusSq
  rw [Fin.sum_univ_succAbove _ c.1]
  simp only [decode,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  split_ifs <;> simp <;> ring

theorem inverse_power_decode {m N : ℕ} (c : CylinderCode m) :
    1/frequencyLength (decode N c)^(2*(m+1))=
      cylinderWeight (m+1) m N c.2.2 := by
  have hsq : frequencyLength (decode N c)^2=radiusSq (decode N c) :=
    Real.sq_sqrt (radiusSq_nonneg _)
  rw [pow_mul,hsq,radiusSq_decode]
  unfold cylinderWeight sliceWeight
  rw [Real.rpow_neg (add_nonneg (sq_nonneg _) (radiusSq_nonneg _)),
    show (m:ℝ)+1=((m+1:ℕ):ℝ) by push_cast; rfl,Real.rpow_natCast,one_div]

def codeWeight (m N : ℕ) (c : CylinderCode m) : ℝ := cylinderWeight (m+1) m N c.2.2

theorem codeWeight_nonneg (m N : ℕ) (c : CylinderCode m) : 0≤codeWeight m N c :=
  Real.rpow_nonneg (add_nonneg (sq_nonneg _) (radiusSq_nonneg _)) _

theorem codeWeight_summable (m : ℕ) {N : ℕ} (hN : 0<N) : Summable (codeWeight m N) := by
  have hp : ((m:ℝ)+1)/2<(m:ℝ)+1 := by have : (0:ℝ)≤m := Nat.cast_nonneg m; linarith
  have hc := cylinder_summable hp hN
  have hb : Summable (fun c : Bool×(ℕ×(Fin m→ℤ))=>cylinderWeight (m+1) m N c.2) :=
    (summable_prod_of_nonneg (fun c=>codeWeight_nonneg m N (0,c))).mpr
      ⟨fun b=>hc,(hasSum_fintype _).summable⟩
  exact (summable_prod_of_nonneg (codeWeight_nonneg m N)).mpr
    ⟨fun i=>hb,(hasSum_fintype _).summable⟩

theorem codeWeight_tsum_le (m : ℕ) {N : ℕ} (hN : 0<N) :
    (∑' c,codeWeight m N c) ≤ 2*(m+1:ℝ)*cylinderBound (m+1) m N := by
  have hp : ((m:ℝ)+1)/2<(m:ℝ)+1 := by have : (0:ℝ)≤m := Nat.cast_nonneg m; linarith
  have hc := cylinder_summable hp hN
  have hb : Summable (fun c : Bool×(ℕ×(Fin m→ℤ))=>cylinderWeight (m+1) m N c.2) :=
    (summable_prod_of_nonneg (fun c=>codeWeight_nonneg m N (0,c))).mpr
      ⟨fun b=>hc,(hasSum_fintype _).summable⟩
  rw [(codeWeight_summable m hN).tsum_prod' (fun i=>hb)]
  have he : (∑' i : Fin (m+1),∑' c : Bool×(ℕ×(Fin m→ℤ)),codeWeight m N (i,c))=
      2*(m+1:ℝ)*(∑'c,cylinderWeight (m+1) m N c) := by
    simp only [codeWeight]
    rw [hb.tsum_prod' (fun b=>hc)]
    simp [tsum_fintype,Finset.sum_const,mul_comm,mul_left_comm,mul_assoc]
  rw [he]
  exact mul_le_mul_of_nonneg_left (cylinder_tsum_le hp hN) (by positivity)

/-- The source's explicit gamma expression bounds the genuine squared omitted-tail constant. -/
theorem tailConstant_cube_sq_le_succ (m R : ℕ) :
    (tailConstant (cube (m+1) R))^2 ≤
      2*(m+1:ℝ)*cylinderBound (m+1) m (R+1) := by
  rw [tailConstant_sq (by omega)]
  refine (Summable.tsum_le_tsum_of_inj encode encode_injective
    (fun c hc=>codeWeight_nonneg m (R+1) c) (fun k=>?_) (tailConstant_hasSum (by omega) _).summable
    (codeWeight_summable m (by omega))).trans (codeWeight_tsum_le m (by omega))
  rw [← decode_encode k,inverse_power_decode]
  exact le_rfl

/-- Exactly the explicit squared constant in source equation `common-lattice-tail`. -/
def explicitBound (d R : ℕ) : ℝ :=
  2*(d:ℝ)*∑j∈Finset.range d, ((d-1).choose j:ℝ)*Real.pi^((j:ℝ)/2)*
    Real.Gamma ((d:ℝ)-(j:ℝ)/2)/Real.Gamma d *
      (((R+1:ℕ):ℝ)^((j:ℝ)-2*d)+
        ((R+1:ℕ):ℝ)^((j:ℝ)-2*d+1)/(2*d-(j:ℝ)-1))

theorem tailConstant_cube_sq_le {d : ℕ} (hd : 0<d) (R : ℕ) :
    (tailConstant (cube d R))^2 ≤ explicitBound d R := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  simpa only [explicitBound,cylinderBound,Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    using tailConstant_cube_sq_le_succ m R

theorem explicitBound_nonneg {d : ℕ} (hd : 0<d) (R : ℕ) : 0≤explicitBound d R :=
  (sq_nonneg _).trans (tailConstant_cube_sq_le hd R)

theorem tailConstant_cube_le {d : ℕ} (hd : 0<d) (R : ℕ) :
    tailConstant (cube d R) ≤ Real.sqrt (explicitBound d R) := by
  exact (Real.le_sqrt (tailConstant_nonneg _) (explicitBound_nonneg hd R)).mpr
    (tailConstant_cube_sq_le hd R)

/-- The rigorous uniform omitted-potential bound used in every grid iteration. -/
theorem omitted_cube_potential_bound {d : ℕ} (hd : 0<d) (R : ℕ)
    (f : Torus d→ℝ) (hf : MemLp f 2 (torusMeasure d)) (x : Torus d) :
    ‖omittedPotential (cube d R) (fourierVector f hf) x‖ ≤
      Real.sqrt (explicitBound d R)*Real.sqrt (∫y,(f y)^2 ∂torusMeasure d) :=
  (omittedPotential_raw_bound (cube d R) f hf x).trans
    (mul_le_mul_of_nonneg_right (tailConstant_cube_le hd R) (Real.sqrt_nonneg _))

#print axioms tailConstant_cube_sq_le
#print axioms omitted_cube_potential_bound
end BecknerOnofri.HighDim.CubeLatticeTail
