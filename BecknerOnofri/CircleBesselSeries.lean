import BecknerOnofri.CircleBesselDefinitions
import BecknerOnofri.CircleBesselDifferential

noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar
open GibbsTrialLower

theorem bessel_series_eq (n : ℕ) (h : ℝ) : bessel n h=∑' j : ℕ,besselOrderTerm h n j := by
  apply tsum_congr
  intro j
  unfold besselOrderTerm
  rw [show 2*j+n=(j+n)+j by omega,pow_add]
  congr 1
  ring

theorem bessel_zero_eq (h : ℝ) : bessel 0 h=besselI0Two h := by
  unfold bessel besselI0Two
  apply tsum_congr
  intro j
  simp only [Nat.add_zero,pow_two]

theorem besselMoment_eq (n : ℕ) (h : ℝ) : besselMoment n h=besselRatio h n := by
  rw [besselMoment,bessel_series_eq,bessel_zero_eq]
  rfl

theorem besselMoment_derivative (n : ℕ) (hn : 1≤n) (h : ℝ) :
    HasDerivAt (besselMoment n)
      (besselMoment (n-1) h+besselMoment (n+1) h-2*besselMoment n h*besselMoment 1 h) h := by
  have hd := besselRatio_derivative h (n:ℤ)
  have he : ((n:ℤ)-1).natAbs=n-1 := by omega
  have he' : ((n:ℤ)+1).natAbs=n+1 := by omega
  have hf : besselMoment n=(fun a => besselRatio a n) := funext (besselMoment_eq n)
  rw [hf]
  simpa only [besselMoment_eq,Int.natAbs_natCast,he,he'] using hd

theorem besselMoment_mono (n : ℕ) : MonotoneOn (besselMoment n) (Set.Ici 0) := by
  have hf : besselMoment n=(fun a => besselRatio a n) := funext (besselMoment_eq n)
  rw [hf]
  simpa only [Int.natAbs_natCast] using besselRatio_mono (n:ℤ)

theorem besselMoment_first_strictMono : StrictMono (besselMoment 1) := by
  have hf : besselMoment 1=(fun a => besselRatio a 1) := funext (besselMoment_eq 1)
  rw [hf]
  exact besselRatio_first_strictMono

#print axioms besselMoment_derivative
#print axioms besselMoment_first_strictMono
end BecknerOnofri.HighDim.CircleScalar
