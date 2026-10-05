module

public import BecknerOnofri.SpinTangentPolytope

@[expose] public section

/-! Sign-face perturbations for the thirteen-state tangent polytope. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Set
namespace BecknerOnofri.HighDim.Spin

def coordinateSign (q : Count → ℝ) (j : Count) : ℝ := if 0 ≤ q j then 1 else -1

theorem abs_perturbation (x y : ℝ) (h : |y| ≤ |x|) :
    |x+y| = |x|+(if 0 ≤ x then 1 else -1)*y := by
  by_cases hx : 0 ≤ x
  · have hy := (abs_le.mp (h.trans_eq (abs_of_nonneg hx))).1
    rw [if_pos hx,abs_of_nonneg hx,abs_of_nonneg (by linarith : 0 ≤ x+y)]
    ring
  · have hx' : x < 0 := lt_of_not_ge hx
    have hy := (abs_le.mp (h.trans_eq (abs_of_neg hx'))).2
    rw [if_neg hx,abs_of_neg hx',abs_of_nonpos (by linarith : x+y ≤ 0)]
    ring

/-- A single positive step works simultaneously on every nonzero coordinate. -/
theorem exists_sign_preserving_step (q v : Count → ℝ)
    (hs : ∀ j,q j=0 → v j=0) :
    ∃ ε : ℝ,0<ε ∧ ∀ j,|ε*v j|≤|q j| := by
  let R : ℝ := ∑ j : Count,|v j|/|q j|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => div_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨1/(1+R),by positivity,?_⟩
  intro j
  by_cases hq : q j=0
  · simp [hq,hs j hq]
  have hp : 0 < |q j| := abs_pos.mpr hq
  have ht : |v j|/|q j|≤R :=
    Finset.single_le_sum (f:=fun i : Count => |v i|/|q i|) (fun i _ => div_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
  have hv : |v j| ≤ |q j| * (1+R) := by
    have h := (div_le_iff₀ hp).mp ht
    nlinarith
  rw [abs_mul,abs_of_pos (show 0<1/(1+R) by positivity)]
  calc
    _ = |v j|/(1+R) := by ring
    _ ≤ _ := (div_le_iff₀ (by positivity)).mpr hv

theorem l1_perturbation (q v : Count → ℝ) (ε : ℝ)
    (hs : ∀ j,|ε*v j|≤|q j|)
    (hz : (∑ j : Count,coordinateSign q j*v j)=0) :
    l1 (q+ε•v)=l1 q := by
  unfold l1
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [abs_perturbation _ _ (hs _)]
  rw [Finset.sum_add_distrib]
  have he : (∑ j : Count,(if 0≤q j then (1:ℝ) else -1)*(ε*v j))=
      ε*(∑ j : Count,coordinateSign q j*v j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold coordinateSign
    ring
  rw [he,hz,mul_zero,add_zero]

/-- Extremality rules out any nonzero direction preserving the three affine
constraints within the sign face. -/
theorem extreme_direction_eq_zero {q v : Count → ℝ}
    (hq : q ∈ tangentPolytope.extremePoints ℝ)
    (hs : ∀ j,q j=0 → v j=0)
    (hmass : (∑ j : Count,v j)=0) (hmean : mean v=0)
    (hsign : (∑ j : Count,coordinateSign q j*v j)=0) : v=0 := by
  obtain ⟨ε,hε,hstep⟩ := exists_sign_preserving_step q v hs
  have hmem (a : ℝ) (ha : ∀ j,|a*v j|≤|q j|) : q+a•v ∈ tangentPolytope := by
    refine ⟨?_,?_,?_,?_⟩
    · simp [hq.1.1,hs 0 hq.1.1]
    · simp [Finset.sum_add_distrib,← Finset.mul_sum,hq.1.2.1,hmass]
    · have h := mean_linear_combination q v 1 a
      simpa [hmean,hq.1.2.2.1] using h
    · rw [l1_perturbation q v a ha hsign]
      exact hq.1.2.2.2
  have hplus := hmem ε hstep
  have hminus : q-ε•v ∈ tangentPolytope := by
    have h := hmem (-ε) (by intro j; simpa using hstep j)
    simpa [neg_smul,sub_eq_add_neg] using h
  have he : q+ε•v=q := hq.2 hplus hminus (mem_openSegment_add_sub q (ε•v))
  ext j
  have hj := congrFun he j
  have hv : ε*v j=0 := by
    change q j+ε*v j=q j at hj
    linarith
  exact (mul_eq_zero.mp hv).resolve_left hε.ne'

/-- Extension by zero from the actual nonzero coordinates. -/
def supportExtension (q : Count → ℝ) :
    ({j : Count // q j ≠ 0} → ℝ) →ₗ[ℝ] (Count → ℝ) := by
  classical
  exact {
    toFun := fun v j => if h : q j ≠ 0 then v ⟨j,h⟩ else 0
    map_add' := by intros; ext j; dsimp; split_ifs <;> simp
    map_smul' := by intros; ext j; dsimp; split_ifs <;> simp }

def faceConstraintMap (q : Count → ℝ) : (Count → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![∑ j : Count,v j, mean v, ∑ j : Count,coordinateSign q j*v j]
  map_add' v w := by
    ext k
    fin_cases k <;>
      simp [mean,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a v := by
    ext k
    fin_cases k <;>
      simp [mean,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_left_comm,mul_assoc]

/-- The three sign-face constraints inject the support space of an extreme
point into ℝ³. This is the dimension argument in Lemma 5.18. -/
theorem extreme_support_card_le_three {q : Count → ℝ}
    (hq : q ∈ tangentPolytope.extremePoints ℝ) :
    Fintype.card {j : Count // q j ≠ 0} ≤ 3 := by
  classical
  let T := (faceConstraintMap q).comp (supportExtension q)
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have he : supportExtension q v=0 := by
      apply extreme_direction_eq_zero hq
      · intro j hj
        simp [supportExtension,hj]
      · simpa [T,faceConstraintMap] using h0
      · simpa [T,faceConstraintMap] using h1
      · simpa [T,faceConstraintMap] using h2
    ext j
    have h := congrFun he j.val
    simpa [supportExtension,j.property] using h
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using hd

#print axioms extreme_direction_eq_zero
#print axioms extreme_support_card_le_three
end BecknerOnofri.HighDim.Spin
