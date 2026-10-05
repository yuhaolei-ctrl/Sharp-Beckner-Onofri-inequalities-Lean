import Legacy.BecknerOnofri.WienerFourier

/-! Exponentiation of a one-sided Fourier series has no negative frequencies.
This supplies one algebraic ingredient of the manuscript's outer construction. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

theorem convolution_nonnegative_support {d : ℕ} (i : Fin d)
    (a b : Frequency d → ℂ)
    (ha : ∀ k,k i<0 → a k=0) (hb : ∀ k,k i<0 → b k=0)
    (k : Frequency d) (hk : k i<0) : convolution a b k=0 := by
  unfold convolution grouped
  apply HasSum.tsum_eq
  apply HasSum.congr_fun hasSum_zero
  intro p
  change a p.val.1*b p.val.2=0
  have hp : p.val.1+p.val.2=k := p.property
  have hi : p.val.1 i+p.val.2 i=k i := congrFun hp i
  by_cases h : p.val.1 i<0
  · rw [ha _ h,zero_mul]
  · rw [hb _ (by omega),mul_zero]

theorem power_nonnegative_support {d : ℕ} (i : Fin d) (a : Frequency d → ℂ)
    (ha : ∀ k,k i<0 → a k=0) (n : ℕ) (k : Frequency d) (hk : k i<0) :
    convolutionPower a n k=0 := by
  classical
  induction n generalizing k with
  | zero =>
    have hk0 : k≠0 := by intro he; simp [he] at hk
    simp [convolutionPower,hk0]
  | succ n ih => exact convolution_nonnegative_support i _ _ ih ha k hk

theorem exponential_nonnegative_support {d : ℕ} (i : Fin d) (a : Frequency d → ℂ)
    (ha : ∀ k,k i<0 → a k=0) (k : Frequency d) (hk : k i<0) :
    exponentialCoefficients a k=0 := by
  unfold exponentialCoefficients
  apply HasSum.tsum_eq
  apply HasSum.congr_fun hasSum_zero
  intro n
  rw [power_nonnegative_support i a ha n k hk,mul_zero]

theorem exponential_fourier_nonnegative_support {d : ℕ} (i : Fin d)
    (a : Frequency d → ℂ) (hs : Summable (fun k => ‖a k‖))
    (ha : ∀ k,k i<0 → a k=0) (k : Frequency d) (hk : k i<0) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k=0 := by
  rw [exponential_coefficient a hs]
  exact exponential_nonnegative_support i a ha k hk

#print axioms exponential_nonnegative_support
#print axioms exponential_fourier_nonnegative_support
end BecknerOnofri.HighDim.CircleOuter
