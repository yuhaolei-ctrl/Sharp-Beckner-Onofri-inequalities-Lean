import BecknerOnofri.GeneralEuler.Regularity
import Legacy.BecknerOnofri.SteinerSelection
import Legacy.BecknerOnofri.ChebyshevProfileIdentification

/-! Actual closed-cube smooth profiles for the smooth Euler potential and
Gibbs density, identified with their concrete Fourier coefficients. -/
open Legacy.BecknerOnofri
namespace BecknerOnofri.GeneralEuler.CosineProfile
open Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open WienerFourier SmoothFourier RadialWiener SteinerSelection ChebyshevProfile
open scoped ContDiff

theorem real_representative_fourier {d : ℕ} (u : TorusL2 d)
    (hs : Summable (fun k => ‖fourierIsometry d u k‖)) (hr : RealPotential u) (k : Frequency d) :
    densityFourier (fun x => (representative u x).re) k = fourierIsometry d u k := by
  have he : (fun x => ((representative u x).re : ℂ)) = representative u := by
    funext x
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (representative_real u hs hr x).symm
  change UnitAddTorus.mFourierCoeff (fun x => ((representative u x).re : ℂ)) k = _
  rw [he, representative_coefficient u hs]

theorem potential_profile {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hE : Regularity.Data A u)
    (hSteiner : Steiner (fun x => (representative u x).re)) :
    ContDiffOn ℝ ∞ (profile (fourierIsometry d u)) (closedCube d) ∧
      ∀ x : Fin d → ℝ, (representative u (quotient x)).re =
        profile (fourierIsometry d u) (cosinePoint x) := by
  have hs := Regularity.fourier_summable hd hR hA hu hE
  have he : densityFourier (fun x => (representative u x).re) = fourierIsometry d u :=
    funext (real_representative_fourier u hs hu.1)
  have h := continuous_profile_factorization (fun x => (representative u x).re)
    (Complex.continuous_re.comp (representative_continuous u hs))
    (fun m => by rw [he]; exact Regularity.radialSummable hd hR hA hu hE m) hSteiner.1
  rwa [he] at h

theorem density_profile {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 0 < A) {u : TorusL2 d} (hu : Admissible u)
    (hE : Regularity.Data A u)
    (hSteiner : Steiner (smoothGibbsValue u)) :
    ContDiffOn ℝ ∞ (profile (densityFourier (gibbsValue u))) (closedCube d) ∧
      ∀ x : Fin d → ℝ, smoothGibbsValue u (quotient x) =
        profile (densityFourier (gibbsValue u)) (cosinePoint x) := by
  have hs := Regularity.fourier_summable hd hR hA hu hE
  have he : densityFourier (smoothGibbsValue u) = densityFourier (gibbsValue u) :=
    funext (smoothGibbsDensity_fourier hR hu hs)
  have h := continuous_profile_factorization (smoothGibbsValue u)
    (smoothGibbsValue_continuous u hs)
    (fun m => by rw [he]; exact Regularity.density_radialSummable hd hR hA hu hE m) hSteiner.1
  rwa [he] at h

#print axioms potential_profile
#print axioms density_profile
end BecknerOnofri.GeneralEuler.CosineProfile
