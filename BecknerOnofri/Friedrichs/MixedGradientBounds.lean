module

public import BecknerOnofri.Friedrichs.MixedScalarCutoff
public import BecknerOnofri.Friedrichs.MixedCompactBounds

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma profile_compact_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ K : ℝ,0≤K ∧ ∀ t∈Icc 0 (2*Real.pi),|f t|≤K ∧ |deriv f t|≤K := by
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0:ℝ) (2*Real.pi)) hf.continuous.continuousOn
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0:ℝ) (2*Real.pi)) (contDiff_infty_iff_deriv.mp hf).2.continuous.continuousOn
  refine ⟨max 0 (max A B),le_max_left _ _,?_⟩
  intro t ht
  exact ⟨(hA t ht).trans ((le_max_left A B).trans (le_max_right _ _)),
    (hB t ht).trans ((le_max_right A B).trans (le_max_right _ _))⟩

lemma cutoff_profile_joint_bound (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hend : m≠0 → f 0=0 ∧ f Real.pi=0) :
    ∃ C : ℝ,0≤C ∧ ∀ δ,0<δ → ∀ t,t∈Icc 0 (2*Real.pi) → (m≠0 → t∈Ioo 0 Real.pi) →
      |f t|≤C ∧ |deriv f t|≤C ∧ |scalarCutoff m δ t*f t|≤C ∧
      |deriv (fun s => scalarCutoff m δ s*f s) t|≤C := by
  obtain ⟨K,hK,hKb⟩ := profile_compact_bound hf
  obtain ⟨B,hB,hBb⟩ := scalarCutoff_derivative_bound m hf hend
  refine ⟨K+B,add_nonneg hK hB,?_⟩
  intro δ hδ t ht hi
  have hcut := scalarCutoff_mem m δ t
  have hnorm : |scalarCutoff m δ t|≤1 := by simpa only [abs_of_nonneg hcut.1] using hcut.2
  have hval : |scalarCutoff m δ t*f t|≤K := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hnorm).trans (hKb t ht).1
  have hder : |scalarCutoff m δ t*deriv f t|≤K := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hnorm).trans (hKb t ht).2
  refine ⟨(hKb t ht).1.trans (le_add_of_nonneg_right hB),
    (hKb t ht).2.trans (le_add_of_nonneg_right hB),hval.trans (le_add_of_nonneg_right hB),?_⟩
  rw [scalarCutoff_product_deriv m (hf.differentiable (by simp))]
  exact (abs_add_le _ _).trans (by linarith [hBb δ hδ t hi])

lemma partialDerivative_productProfile_bound {d : ℕ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,Differentiable ℝ (f j)) (C : Fin d → ℝ) (hC : ∀ j,0≤C j)
    (i : Fin d) (x : Space d) (hval : ∀ j,|f j (x j)|≤C j)
    (hder : |deriv (f i) (x i)|≤C i) :
    |partialDerivative i (productProfile f) x|≤∏ j,C j := by
  rw [partialDerivative_productProfile f hf,abs_mul,Finset.abs_prod]
  have hp : (∏ j∈Finset.univ.erase i,|f j (x j)|)≤∏ j∈Finset.univ.erase i,C j :=
    Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hval j)
  calc
    _ ≤ (∏ j∈Finset.univ.erase i,C j)*C i :=
      mul_le_mul hp hder (abs_nonneg _) (Finset.prod_nonneg (fun j _ => hC j))
    _ = _ := Finset.prod_erase_mul _ _ (Finset.mem_univ i)

lemma partialDerivative_productProfile_continuous {d : ℕ} (f : Fin d → ℝ → ℝ)
    (hf : ∀ j,ContDiff ℝ ∞ (f j)) (i : Fin d) :
    Continuous (partialDerivative i (productProfile f)) := by
  have he : partialDerivative i (productProfile f)=(fun x =>
      (∏ j∈Finset.univ.erase i,f j (x j))*deriv (f i) (x i)) :=
    funext (fun x => partialDerivative_productProfile f (fun j => (hf j).differentiable (by simp)) i x)
  rw [he]
  exact (continuous_finsetProd _ (fun j _ => (hf j).continuous.comp (continuous_apply j))).mul
    ((contDiff_infty_iff_deriv.mp (hf i)).2.continuous.comp (continuous_apply i))

#print axioms cutoff_profile_joint_bound
#print axioms partialDerivative_productProfile_bound
end BecknerOnofri.Friedrichs.MixedSpatial
