module

public import Legacy.BecknerOnofri.SubcriticalWiener

@[expose] public section

/-! Analytic input for a general smooth Euler pair. This internal interface
contains rapid Fourier decay and the actual Fourier Euler equation, not
variational maximality. The raw smooth-pair bridge derives both fields. -/
noncomputable section
open Legacy.TorusEndpoint Legacy.BecknerOnofri
namespace BecknerOnofri.GeneralEuler.Regularity
open TorusSobolev SubcriticalAttainment SubcriticalEuler RadialWiener

structure Data {d : ℕ} (A : ℝ) (u : TorusL2 d) : Prop where
  radial : ∀ m : ℕ, RadialSummable (fourierIsometry d u) m
  euler : ∀ k : Frequency d, k ≠ 0 → fourierIsometry d u k =
    ((1/(2*A)*(frequencyRadius k^d)⁻¹ : ℝ) : ℂ)*densityFourier (gibbsValue u) k

variable {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
  (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
  (hE : Data A u)

include hd hR hA hu hE
lemma radialSummable (m : ℕ) : RadialSummable (fourierIsometry d u) m := hE.radial m
lemma fourier_summable : Summable (fun k => ‖fourierIsometry d u k‖) :=
  (radialSummable_zero _).mp (hE.radial 0)
lemma density_radialSummable (m : ℕ) : RadialSummable (densityFourier (gibbsValue u)) m :=
  gibbs_radialSummable u m (hE.radial m) hu.1 (partition u)
omit hd in
lemma fourier_formula {k : Frequency d} (hk : k ≠ 0) : fourierIsometry d u k =
    ((1/(2*A)*(frequencyRadius k^d)⁻¹ : ℝ) : ℂ)*densityFourier (gibbsValue u) k := hE.euler k hk

end BecknerOnofri.GeneralEuler.Regularity
