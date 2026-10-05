import BecknerOnofri.CircleOuterSupport

/-! Real Taylor coefficients are preserved by the actual Fourier exponential. -/
noncomputable section
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

theorem convolution_real {d : ℕ} (a b : Frequency d → ℂ)
    (ha : ∀ k,conj (a k)=a k) (hb : ∀ k,conj (b k)=b k) (k : Frequency d) :
    conj (convolution a b k)=convolution a b k := by
  unfold convolution grouped
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro p
  change conj (a p.val.1*b p.val.2)=a p.val.1*b p.val.2
  rw [map_mul,ha,hb]

theorem power_real {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ k,conj (a k)=a k) (n : ℕ) (k : Frequency d) :
    conj (convolutionPower a n k)=convolutionPower a n k := by
  classical
  induction n generalizing k with
  | zero => simp only [convolutionPower]; split_ifs <;> simp
  | succ n ih => exact convolution_real _ _ ih ha k

theorem exponential_real {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ k,conj (a k)=a k) (k : Frequency d) :
    conj (exponentialCoefficients a k)=exponentialCoefficients a k := by
  unfold exponentialCoefficients
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_mul,power_real a ha]
  simp

#print axioms exponential_real
end BecknerOnofri.HighDim.CircleOuter
