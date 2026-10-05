module

public import BecknerOnofri.BinarySpinChannel

@[expose] public section

/-! The binomial coefficients in the thirteen-state matrix are the actual
joint spin moments on each count class, verified over the full finite space. -/
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem jointSpin_cast (S : Finset (Fin 12)) (σ : Configuration) :
    (jointSpinQ S σ:ℝ)=jointSpin S σ := by
  simp [jointSpinQ,jointSpin]

/-- A finite combinatorial identity, not a numerical enclosure. -/
theorem count_joint_moment_rational : ∀ s : Order,∀ j : Count,
    (∑ σ ∈ countClass j,jointSpinQ (firstCoordinates s) σ)=
      ((12:ℕ).choose j.val:ℚ)*momentQ s j := by
  decide +kernel

theorem count_joint_moment (s : Order) (j : Count) :
    (∑ σ ∈ countClass j,jointSpin (firstCoordinates s) σ)=
      ((12:ℕ).choose j.val:ℝ)*moment s j := by
  have h := congrArg (fun a : ℚ => (a:ℝ)) (count_joint_moment_rational s j)
  simpa only [Rat.cast_sum,jointSpin_cast,Rat.cast_mul,Rat.cast_natCast,moment] using h

theorem exchangeable_joint_moment {ν : Configuration → ℝ} (hν : Exchangeable ν) (s : Order) :
    (∑ σ : Configuration,ν σ*jointSpin (firstCoordinates s) σ)=
      ∑ j : Count,moment s j*countLaw ν j := by
  rw [sum_count_classes]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ σ ∈ countClass j,
        (countLaw ν j/((12:ℕ).choose j.val:ℝ))*jointSpin (firstCoordinates s) σ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      have hh := (countClass_mem j σ).mp hσ
      have he := law_eq_countLaw_div hν σ
      rw [he,hh,show σ.card=j.val from congrArg Fin.val hh]
    _ = _ := by
      rw [← Finset.mul_sum,count_joint_moment]
      field_simp [(countClass_pos j).ne']

/-- Exactly the weighted cube-spin energy used in equation (5.138). -/
theorem exchangeable_energy {ν : Configuration → ℝ} (hν : Exchangeable ν) :
    (∑ s : Order,weight s*(∑ σ : Configuration,ν σ*jointSpin (firstCoordinates s) σ)^2)=
      quadratic (countLaw ν) := by
  simp_rw [exchangeable_joint_moment hν]
  exact (quadratic_eq_sum _).symm

#print axioms exchangeable_energy
end BecknerOnofri.HighDim.Spin
