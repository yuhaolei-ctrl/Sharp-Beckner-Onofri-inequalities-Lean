import BecknerOnofri.SpinPosteriorJensen
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! The actual finite tree of spin prefixes, with no duplicate prefix events. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin
open EntropyShearer ConditionalEntropy

def prefixSet (k : ℕ) : Finset (Fin 12) := Finset.univ.filter (fun j => j.val < k)

@[simp] theorem mem_prefixSet {k : ℕ} {j : Fin 12} : j ∈ prefixSet k ↔ j.val < k := by
  simp [prefixSet]

@[simp] theorem prefixSet_zero : prefixSet 0 = ∅ := by ext j; simp

@[simp] theorem prefixSet_twelve : prefixSet 12 = Finset.univ := by
  ext j
  simp [j.isLt]

theorem prefixSet_step (i : Fin 12) : prefixSet (i.val + 1) = insert i (prefixSet i.val) := by
  ext j
  simp only [mem_prefixSet, Finset.mem_insert]
  constructor
  · intro hj
    by_cases he : j = i
    · exact Or.inl he
    · right
      have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
  · rintro (rfl | h) <;> omega

theorem prefixLikelihood_congr (k : ℕ) {σ τ : Configuration}
    (h : ∀ j ∈ prefixSet k, j ∈ σ ↔ j ∈ τ) (x : Torus 12) :
    prefixLikelihood k σ x = prefixLikelihood k τ x := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [h j hj]

theorem prefixLikelihood_insert (i : Fin 12) (σ : Configuration) (x : Torus 12) :
    prefixLikelihood i.val (insert i σ) x = prefixLikelihood i.val σ x := by
  apply prefixLikelihood_congr
  intro j hj
  have hne : j ≠ i := by
    intro he
    subst j
    simpa using hj
  simp [hne]

theorem prefixLikelihood_step (i : Fin 12) (σ : Configuration) (x : Torus 12) :
    prefixLikelihood (i.val + 1) σ x =
      (if i ∈ σ then (1 + torusCosines x i) / 2 else (1 - torusCosines x i) / 2) *
        prefixLikelihood i.val σ x := by
  change (∏ j ∈ prefixSet (i.val + 1), _) = _
  rw [prefixSet_step, Finset.prod_insert (by simp)]
  rfl

theorem prefixLikelihood_children (i : Fin 12) {σ : Configuration}
    (hσ : σ ⊆ prefixSet i.val) (x : Torus 12) :
    prefixLikelihood (i.val + 1) (insert i σ) x + prefixLikelihood (i.val + 1) σ x =
        prefixLikelihood i.val σ x ∧
    prefixLikelihood (i.val + 1) (insert i σ) x - prefixLikelihood (i.val + 1) σ x =
        prefixLikelihood i.val σ x * torusCosines x i := by
  have hi : i ∉ σ := fun h => by simpa using hσ h
  rw [prefixLikelihood_step, prefixLikelihood_step, prefixLikelihood_insert]
  simp only [Finset.mem_insert_self, ite_true, hi, ite_false]
  constructor <;> ring

theorem prefixLikelihood_sum (k : ℕ) (hk : k ≤ 12) (x : Torus 12) :
    (∑ σ ∈ (prefixSet k).powerset, prefixLikelihood k σ x) = 1 := by
  induction k with
  | zero => simp [prefixLikelihood]
  | succ k ih =>
    let i : Fin 12 := ⟨k, by omega⟩
    change (∑ σ ∈ (prefixSet (i.val + 1)).powerset, prefixLikelihood (i.val + 1) σ x) = 1
    rw [prefixSet_step, Finset.sum_powerset_insert (by simp : i ∉ prefixSet i.val),
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ σ ∈ (prefixSet i.val).powerset, prefixLikelihood i.val σ x := by
        apply Finset.sum_congr rfl
        intro σ hσ
        simpa only [add_comm] using
          (prefixLikelihood_children i (Finset.mem_powerset.mp hσ) x).1
      _ = 1 := ih (by omega)

theorem prefixLikelihood_full (σ : Configuration) (x : Torus 12) :
    prefixLikelihood 12 σ x = channel (torusCosines x) σ := by
  change (∏ j ∈ prefixSet 12, _) = _
  rw [prefixSet_twelve]
  rw [← Finset.prod_mul_prod_compl σ]
  unfold channel
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp [hj]
  · apply Finset.prod_congr rfl
    intro j hj
    simp [Finset.mem_compl.mp hj]

def prefixMass (f : Torus 12 → ℝ) (k : ℕ) (σ : Configuration) : ℝ :=
  ∫ x, f x * prefixLikelihood k σ x ∂torusMeasure 12

theorem prefixMass_positive {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (k : ℕ) (σ : Configuration) : 0 < prefixMass f k σ := prefix_mass_pos hf k σ

theorem prefixMass_children {f : Torus 12 → ℝ} (hf : PositiveBounded f)
    (i : Fin 12) {σ : Configuration} (hσ : σ ⊆ prefixSet i.val) :
    prefixMass f (i.val + 1) (insert i σ) + prefixMass f (i.val + 1) σ = prefixMass f i.val σ ∧
    prefixMass f (i.val + 1) (insert i σ) - prefixMass f (i.val + 1) σ =
      ∫ x, f x * (prefixLikelihood i.val σ x * torusCosines x i) ∂torusMeasure 12 := by
  have hi (k : ℕ) (τ : Configuration) := (hf.bounded.mul (prefixLikelihood_bounded k τ)).integrable
  unfold prefixMass
  constructor
  · rw [← integral_add (hi _ _) (hi _ _)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← mul_add, (prefixLikelihood_children i hσ x).1]
  · rw [← integral_sub (hi _ _) (hi _ _)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [← mul_sub, (prefixLikelihood_children i hσ x).2]

#print axioms prefixLikelihood_sum
#print axioms prefixMass_children
end BecknerOnofri.HighDim.Spin
