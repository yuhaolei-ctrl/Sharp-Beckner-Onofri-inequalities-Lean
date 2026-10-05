import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Uniform Lipschitz approximation on a compact metric space. The lattice
Stone-Weierstrass argument uses affine distance functions as separators. -/
noncomputable section
open Set
open scoped Topology NNReal
namespace BecknerOnofri.RearrangementApproximation

theorem exists_lipschitz_uniform_approx {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : C(X,ℝ)) {ε : ℝ} (hε : 0<ε) :
    ∃ g : C(X,ℝ), (∃ K : ℝ≥0,LipschitzWith K g) ∧ ∀ x,‖f x-g x‖<ε := by
  let S : Set C(X,ℝ) := {g | ∃ K : ℝ≥0,LipschitzWith K g}
  have hnonempty : S.Nonempty := ⟨ContinuousMap.const X 0,0,LipschitzWith.const 0⟩
  have hinf : ∀ᵉ (g∈S) (h∈S),g⊓h∈S := by
    rintro g ⟨K,hK⟩ h ⟨L,hL⟩
    exact ⟨max K L,hK.min hL⟩
  have hsup : ∀ᵉ (g∈S) (h∈S),g⊔h∈S := by
    rintro g ⟨K,hK⟩ h ⟨L,hL⟩
    exact ⟨max K L,hK.max hL⟩
  have hsep : S.SeparatesPointsStrongly := by
    intro v x y
    by_cases hxy : x=y
    · exact ⟨ContinuousMap.const X (v x),⟨0,LipschitzWith.const (v x)⟩,rfl,by simp [hxy]⟩
    · let c := (v y-v x)/dist x y
      let g : C(X,ℝ) := ⟨fun z => v x+c*dist x z,by fun_prop⟩
      have hg : LipschitzWith ‖c‖₊ g := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        have h := mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using abs_dist_sub_le z w x) (abs_nonneg c)
        simpa only [g,ContinuousMap.coe_mk,dist_eq_norm,Real.norm_eq_abs,coe_nnnorm] using (show |v x+c*dist x z-(v x+c*dist x w)|≤|c| *dist z w by
            rw [show v x+c*dist x z-(v x+c*dist x w)=c*(dist x z-dist x w) by ring,abs_mul]
            exact h)
      refine ⟨g,⟨‖c‖₊,hg⟩,?_,?_⟩
      · simp [g]
      · dsimp [g,c]
        rw [div_mul_cancel₀ _ (dist_ne_zero.mpr hxy)]
        ring
  have hclosure : closure S=Set.univ :=
    ContinuousMap.sublattice_closure_eq_top S hnonempty hinf hsup hsep
  have hf : f∈closure S := by rw [hclosure]; trivial
  obtain ⟨g,hg,hgf⟩ := Metric.mem_closure_iff.mp hf ε hε
  refine ⟨g,hg,fun x => ?_⟩
  have h := (ContinuousMap.dist_apply_le_dist (f := f) (g := g) x).trans_lt hgf
  simpa only [dist_eq_norm] using h

#print axioms exists_lipschitz_uniform_approx
end BecknerOnofri.RearrangementApproximation
