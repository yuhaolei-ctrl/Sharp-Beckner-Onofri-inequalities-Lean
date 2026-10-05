module

public import BecknerOnofri.ConditionalEntropyDefinitions
public import BecknerOnofri.EntropyShearer.Contraction

@[expose] public section

/-! The ordered entropy chain rule for genuine Haar conditional densities. -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace BecknerOnofri.HighDim.ConditionalEntropy
open EntropyShearer

@[simp] theorem mem_suffixCoordinates {d k : ℕ} {j : Fin d} :
    j ∈ suffixCoordinates d k ↔ k ≤ j.val := by
  simp [suffixCoordinates]

theorem suffix_zero (d : ℕ) : suffixCoordinates d 0 = Finset.univ := by
  ext j
  simp

theorem suffix_last (d : ℕ) : suffixCoordinates d d = ∅ := by
  ext j
  simp [Nat.not_le_of_lt j.isLt]

theorem suffix_step {d : ℕ} (i : Fin d) :
    suffixCoordinates d i.val = {i} ∪ suffixCoordinates d (i.val + 1) := by
  ext j
  simp only [mem_suffixCoordinates, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    by_cases he : j = i
    · exact Or.inl he
    · right
      have : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
  · rintro (rfl | h) <;> omega

theorem suffix_step_disjoint {d : ℕ} (i : Fin d) :
    Disjoint ({i} : Finset (Fin d)) (suffixCoordinates d (i.val + 1)) := by
  simp

theorem prefix_eq_avg {d : ℕ} (f : Torus d → ℝ) (k : ℕ) :
    prefixDensity f k = avg (suffixCoordinates d k) f := rfl

@[simp] theorem prefix_zero {d : ℕ} (f : Torus d → ℝ) :
    prefixDensity f 0 = fun _ => ∫ x, f x ∂torusMeasure d := by
  rw [prefix_eq_avg, suffix_zero, avg_univ]

@[simp] theorem prefix_last {d : ℕ} (f : Torus d → ℝ) :
    prefixDensity f d = f := by
  rw [prefix_eq_avg, suffix_last, avg_empty]

theorem prefix_positive {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (k : ℕ) : PositiveBounded (prefixDensity f k) :=
  hf.avg _

theorem prefix_step {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) (i : Fin d) :
    prefixDensity f i.val = avg {i} (prefixDensity f (i.val + 1)) := by
  rw [prefix_eq_avg, suffix_step, avg_union (suffix_step_disjoint i) hf]
  rfl

theorem prefix_update {d : ℕ} {f : Torus d → ℝ}
    (hf : BoundedMeasurable f) (i : Fin d) (x : Torus d) (z : UnitAddCircle) :
    prefixDensity f i.val (Function.update x i z) = prefixDensity f i.val x := by
  rw [prefix_step hf i]
  rw [update_eq_updateFinset]
  exact avg_update _ _ _ _

theorem conditional_density_positive {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (x : Torus d) (z : UnitAddCircle) :
    0 < conditionalDensity f i x z :=
  div_pos ((prefix_positive hf _).pos _) ((prefix_positive hf _).pos _)

theorem conditional_density_mass {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (x : Torus d) :
    (∫ z, conditionalDensity f i x z ∂AddCircle.haarAddCircle) = 1 := by
  simp only [conditionalDensity, integral_div]
  have h := congrFun (prefix_step hf.bounded i) x
  rw [avg_singleton] at h
  dsimp only at h
  rw [← h, div_self ((prefix_positive hf _).pos _).ne']

theorem conditional_entropy_weighted {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) (x : Torus d) :
    prefixDensity f i.val x * conditionalEntropy f i x =
      avg {i} (fun y => prefixDensity f (i.val + 1) y *
        (Real.log (prefixDensity f (i.val + 1) y) - Real.log (prefixDensity f i.val y))) x := by
  let a := prefixDensity f (i.val + 1)
  let b := prefixDensity f i.val
  have ha : PositiveBounded a := prefix_positive hf _
  have hb : PositiveBounded b := prefix_positive hf _
  rw [avg_singleton]
  simp only [conditionalEntropy, conditionalDensity, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  have he : b (Function.update x i z) = b x := prefix_update hf.bounded i x z
  change b x * (a (Function.update x i z) / b x *
    Real.log (a (Function.update x i z) / b x)) =
      a (Function.update x i z) *
        (Real.log (a (Function.update x i z)) - Real.log (b (Function.update x i z)))
  rw [Real.log_div (ha.pos _).ne' (hb.pos _).ne', he]
  field_simp [(hb.pos x).ne']

theorem conditional_entropy_increment {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (i : Fin d) :
    (∫ x, prefixDensity f i.val x * conditionalEntropy f i x ∂torusMeasure d) =
      entropyIntegral (prefixDensity f (i.val + 1)) -
        entropyIntegral (prefixDensity f i.val) := by
  let a := prefixDensity f (i.val + 1)
  let b := prefixDensity f i.val
  have ha : PositiveBounded a := prefix_positive hf _
  have hb : PositiveBounded b := prefix_positive hf _
  calc
    _ = ∫ x, avg {i} (fun y => a y * (Real.log (a y) - Real.log (b y))) x
        ∂torusMeasure d := integral_congr_ae
          (Filter.Eventually.of_forall (conditional_entropy_weighted hf i))
    _ = relativeEntropy a b := integral_avg {i}
      (ha.bounded.mul (ha.logBounded.sub hb.logBounded))
    _ = _ := by
      have h := entropy_difference ha ({i} : Finset (Fin d))
      have he : avg {i} a = b := (prefix_step hf.bounded i).symm
      rw [he] at h
      exact h

theorem entropy_chain_rule {d : ℕ} {f : Torus d → ℝ}
    (hf : PositiveBounded f) (hmass : (∫ x, f x ∂torusMeasure d) = 1) :
    (∫ x, f x * Real.log (f x) ∂torusMeasure d) =
      ∑ i : Fin d, ∫ x, prefixDensity f i.val x * conditionalEntropy f i x
        ∂torusMeasure d := by
  simp_rw [conditional_entropy_increment hf]
  have htel (n : ℕ) :
      (∑ k ∈ Finset.range n, (entropyIntegral (prefixDensity f (k + 1)) -
        entropyIntegral (prefixDensity f k))) =
        entropyIntegral (prefixDensity f n) - entropyIntegral (prefixDensity f 0) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have ht := htel d
  rw [← Fin.sum_univ_eq_sum_range] at ht
  simpa [entropyIntegral, hmass] using ht.symm

#print axioms entropy_chain_rule

end BecknerOnofri.HighDim.ConditionalEntropy
