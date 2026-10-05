module

public import BecknerOnofri.PressureDuality
public import BecknerOnofri.Constants

@[expose] public section

/-! Transfer of the scalar pressure asymptotic by the exact physical duality.
The pressure asymptotic remains an explicit premise, not an assumed axiom. -/
noncomputable section
namespace BecknerOnofri.HighDim

theorem coefficient_onset_of_pressure {d : ℕ} (hd : 0 < d)
    (hP : ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ β : ℝ, spectralThreshold d < β → β < spectralThreshold d + ε →
        ∃ p : ℝ, pressure d β = (p : EReal) ∧
          |p - (d : ℝ) / (2 * kappa d) * (1 - spectralThreshold d / β) ^ 2| ≤
            C * (β - spectralThreshold d) ^ 3) :
    ∃ ε C : ℝ, 0 < ε ∧ ε < spectralCoefficient d ∧ 0 ≤ C ∧
      ∀ A : ℝ, spectralCoefficient d - ε < A → A < spectralCoefficient d →
        ∃ c : ℝ, coefficientDefect d A = (c : EReal) ∧
          |c - (d : ℝ) / (2 * kappa d) * (1 - A / spectralCoefficient d) ^ 2| ≤
            C * (1 - A / spectralCoefficient d) ^ 3 := by
  obtain ⟨e, C, he, hC, hP⟩ := hP
  let a := spectralCoefficient d
  let s := spectralThreshold d
  have ha : 0 < a := by dsimp [a, spectralCoefficient]; positivity
  have hs : 0 < s := spectralThreshold_pos hd
  let ε := min (a / 2) (a * e / (4 * s))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεa : ε ≤ a / 2 := min_le_left _ _
  have hεe : ε ≤ a * e / (4 * s) := min_le_right _ _
  refine ⟨ε, C * (2 * s) ^ 3, hε, lt_of_le_of_lt hεa (by linarith), by positivity, ?_⟩
  intro A hAl hAu
  change a - ε < A at hAl
  change A < a at hAu
  have hAa : a / 2 < A := by linarith
  have hA : 0 < A := by linarith
  let β := s * a / A
  have hβ : 0 < β := by dsimp [β]; positivity
  have hsβ : s < β := by
    dsimp [β]
    apply (lt_div_iff₀ hA).mpr
    exact mul_lt_mul_of_pos_left hAu hs
  have hβ2 : β < 2 * s := by
    dsimp [β]
    apply (div_lt_iff₀ hA).mpr
    nlinarith
  have hδ : 0 < 1 - A / a := sub_pos.mpr ((div_lt_one ha).mpr hAu)
  have hδe : 1 - A / a < ε / a := by
    rw [sub_div' ha.ne', one_mul]
    exact (div_lt_div_iff_of_pos_right ha).mpr (by linarith)
  have hbe : β - s = β * (1 - A / a) := by dsimp [β]; field_simp
  have hbound : β - s ≤ (2 * s) * (1 - A / a) := by
    rw [hbe]
    exact mul_le_mul_of_nonneg_right hβ2.le hδ.le
  have hbnear : β < s + e := by
    have hsmall : 2 * s * (ε / a) ≤ e / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hεe' := (le_div_iff₀ (by positivity : 0 < 4 * s)).mp hεe
      calc
        _ = (ε * (4 * s)) / a := by ring
        _ ≤ (a * e) / a := div_le_div_of_nonneg_right hεe' ha.le
        _ = e := by field_simp
    have hsmall' := mul_lt_mul_of_pos_left hδe (by positivity : 0 < 2 * s)
    linarith
  obtain ⟨p, hp, hrem⟩ := hP β hsβ hbnear
  have hratio : s / β = A / a := by dsimp [β]; field_simp
  have hcoef : spectralThreshold d / (2 * β * (2 * Real.pi) ^ d) = A := by
    have hσne := (spectralThreshold_pos hd).ne'
    dsimp [β, s, a, spectralCoefficient]
    field_simp
  have hdual := pressure_eq_coefficientDefect hd hβ
  rw [hcoef] at hdual
  refine ⟨p, hdual.symm.trans hp, ?_⟩
  change |p - (d : ℝ) / (2 * kappa d) * (1 - s / β) ^ 2| ≤
    C * (β - s) ^ 3 at hrem
  rw [hratio] at hrem
  apply hrem.trans
  have hpw := pow_le_pow_left₀ (sub_nonneg.mpr hsβ.le) hbound 3
  calc
    C * (β - s) ^ 3 ≤ C * ((2 * s) * (1 - A / a)) ^ 3 :=
      mul_le_mul_of_nonneg_left hpw hC
    _ = _ := by ring

#print axioms coefficient_onset_of_pressure
end BecknerOnofri.HighDim
