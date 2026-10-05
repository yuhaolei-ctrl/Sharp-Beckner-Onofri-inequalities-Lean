module

public import BecknerOnofri.SpinAlgebra
public import BecknerOnofri.SpinCountDefinitions

@[expose] public section

/-! The thirteen-state distribution is the actual count pushforward of an
exchangeable law on twelve binary spins. A finset records the plus spins. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

theorem countClass_mem (j : Count) (σ : Configuration) :
    σ∈countClass j ↔ plusCount σ=j := by
  simp [countClass,plusCount,Fin.ext_iff]

theorem countClass_card (j : Count) : (countClass j).card=(12:ℕ).choose j.val := by
  simp [countClass]

theorem countClass_pos (j : Count) : (0:ℝ)<((12:ℕ).choose j.val:ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : j.val≤12)

theorem sum_count_classes (f : Configuration → ℝ) :
    (∑ σ : Configuration,f σ)=∑ j : Count,∑ σ ∈ countClass j,f σ := by
  have he (j : Count) : Finset.univ.filter (fun σ : Configuration => plusCount σ=j)=countClass j := by
    ext σ
    simp [countClass_mem]
  simpa only [he] using (Finset.sum_fiberwise Finset.univ plusCount f).symm

theorem exchangeable_equal_of_count {ν : Configuration → ℝ} (hν : Exchangeable ν)
    {σ τ : Configuration} (h : plusCount σ=plusCount τ) : ν σ=ν τ := by
  have hc : σ.card=τ.card := congrArg Fin.val h
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_map_finset_eq σ τ hc
  simpa only [hπ] using (hν π σ).symm

theorem countLaw_eq_mul {ν : Configuration → ℝ} (hν : Exchangeable ν) (σ : Configuration) :
    countLaw ν (plusCount σ)=((12:ℕ).choose σ.card:ℝ)*ν σ := by
  unfold countLaw
  calc
    _ = ∑ _τ ∈ countClass (plusCount σ),ν σ := by
      apply Finset.sum_congr rfl
      intro τ hτ
      exact exchangeable_equal_of_count hν ((countClass_mem _ _).mp hτ)
    _ = _ := by simp [countClass_card,plusCount]

theorem law_eq_countLaw_div {ν : Configuration → ℝ} (hν : Exchangeable ν) (σ : Configuration) :
    ν σ=countLaw ν (plusCount σ)/((12:ℕ).choose σ.card:ℝ) := by
  rw [countLaw_eq_mul hν]
  exact (mul_div_cancel_left₀ _ (countClass_pos (plusCount σ)).ne').symm

theorem countLaw_mass (ν : Configuration → ℝ) :
    (∑ j : Count,countLaw ν j)=∑ σ : Configuration,ν σ := by
  exact (sum_count_classes ν).symm

theorem countLaw_nonneg {ν : Configuration → ℝ} (hν : ∀ σ,0≤ν σ) (j : Count) :
    0≤countLaw ν j := Finset.sum_nonneg (fun σ _ => hν σ)

/-- Exact entropy identification, including laws with zero entries. -/
theorem exchangeable_entropy {ν : Configuration → ℝ} (hν : Exchangeable ν) :
    (∑ σ : Configuration,ν σ*Real.log (ν σ/(1/4096)))=
      relativeEntropy (countLaw ν) reference := by
  rw [sum_count_classes]
  unfold relativeEntropy
  apply Finset.sum_congr rfl
  intro j _
  have hc := (countClass_pos j).ne'
  have he (σ : Configuration) (hσ : σ∈countClass j) :
      ν σ=countLaw ν j/((12:ℕ).choose j.val:ℝ) := by
    have hh := (countClass_mem j σ).mp hσ
    simpa only [hh,show σ.card=j.val from congrArg Fin.val hh] using law_eq_countLaw_div hν σ
  calc
    _ = ∑ _σ ∈ countClass j,
        (countLaw ν j/((12:ℕ).choose j.val:ℝ))*Real.log (countLaw ν j/reference j) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [he σ hσ]
      congr 2
      simp only [reference,referenceQ,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
      field_simp
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,countClass_card]
      field_simp

#print axioms exchangeable_entropy
end BecknerOnofri.HighDim.Spin
