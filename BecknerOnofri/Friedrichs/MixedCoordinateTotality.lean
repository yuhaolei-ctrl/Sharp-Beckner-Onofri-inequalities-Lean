import BecknerOnofri.Friedrichs.MixedFullEigenvectors
import BecknerOnofri.Friedrichs.PeriodicTrigonometricTotality
import Legacy.BecknerOnofri.JacobiCompleteness

/-! Totality on each actual mixed coordinate measure, including both periodic parities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.MixedSpatial

lemma periodic_modes_total (f : PeriodicRealL2)
    (h : ∀ (odd : Bool) (n : ℕ), (∫ t in Ioc 0 (2*Real.pi),periodicMode odd n t*f t)=0) : f=0 := by
  apply periodic_trigonometric_total f
  · intro n
    cases n with
    | ofNat n => simpa [periodicMode] using h false n
    | negSucc n =>
      have hn : ((Int.negSucc n:ℤ):ℝ)= -((n+1:ℕ):ℝ) := by push_cast; ring
      simp only [hn,neg_mul,Real.cos_neg]
      exact h false (n+1)
  · intro n
    cases n with
    | ofNat n => simpa [periodicMode] using h true n
    | negSucc n =>
      have hn : ((Int.negSucc n:ℤ):ℝ)= -((n+1:ℕ):ℝ) := by push_cast; ring
      simp only [hn,neg_mul,Real.sin_neg,integral_neg]
      simpa only [periodicMode,ite_true,neg_zero] using congrArg Neg.neg (h true (n+1))

theorem coordinate_fullEigenprofile_total (m : ℕ) (f : Lp ℝ 2 (coordinateMeasure m))
    (h : ∀ (odd : Bool) (n : ℕ), (∫ t, fullEigenprofile m n odd t*f t ∂coordinateMeasure m)=0) : f=0 := by
  cases m with
  | zero =>
    apply periodic_modes_total f
    intro odd n
    simpa [fullEigenprofile,coordinateMeasure] using h odd n
  | succ m =>
    apply Legacy.BecknerOnofri.JacobiEigenfunctions.eq_zero_of_orthogonal_eigenvector f (m+1)
    intro n
    rw [L2.inner_def]
    calc
      _ = ∫ t, Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction (m+1) n t*f t
          ∂Legacy.BecknerOnofri.JacobiEigenfunctions.intervalMeasure := by
        apply integral_congr_ae
        filter_upwards [Legacy.BecknerOnofri.JacobiEigenfunctions.eigenvector_ae_eq (m+1) n] with t ht
        simp only [ht, RCLike.inner_apply,conj_trivial]
      _ = 0 := by
        simpa [fullEigenprofile,coordinateMeasure,Legacy.BecknerOnofri.JacobiEigenfunctions.intervalMeasure,Legacy.BecknerOnofri.JacobiEigenfunctions.eigenfunction,Legacy.BecknerOnofri.JacobiEigenfunctions.polynomial] using h false (n+(m+1))

#print axioms coordinate_fullEigenprofile_total
end BecknerOnofri.Friedrichs.MixedSpatial
