import BecknerOnofri.CircleOuterDefinitions
import BecknerOnofri.CircleOuterReal

/-! One-sided Fourier reconstruction of half a real, even logarithm and the
exact modulus of its exponential on the boundary. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WienerFourier

theorem halfSpectrum_real {d : ℕ} (i : Fin d) (l : Frequency d → ℝ) (k : Frequency d) :
    conj (halfSpectrum i l k)=halfSpectrum i l k := by
  unfold halfSpectrum
  split_ifs <;> simp only [Complex.conj_ofReal,map_zero]

theorem halfSpectrum_norm_le {d : ℕ} (i : Fin d) (l : Frequency d → ℝ) (k : Frequency d) :
    ‖halfSpectrum i l k‖≤‖l k‖ := by
  unfold halfSpectrum
  split_ifs
  · simp only [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [abs_nonneg (l k)]
  · simp
  · simp

theorem halfSpectrum_summable {d : ℕ} (i : Fin d) (l : Frequency d → ℝ)
    (hl : Summable (fun k => ‖l k‖)) : Summable (fun k => ‖halfSpectrum i l k‖) :=
  Summable.of_nonneg_of_le (fun k => norm_nonneg _) (halfSpectrum_norm_le i l) hl

theorem halfSpectrum_negative {d : ℕ} (i : Fin d) (l : Frequency d → ℝ)
    (k : Frequency d) (hk : k i<0) : halfSpectrum i l k=0 := by
  simp [halfSpectrum,ne_of_lt hk,not_lt.mpr hk.le]

theorem halfSpectrum_pair {d : ℕ} (i : Fin d) (l : Frequency d → ℝ)
    (he : ∀ k,l (-k)=l k) (k : Frequency d) :
    halfSpectrum i l k+halfSpectrum i l (-k)=(l k:ℂ) := by
  unfold halfSpectrum
  simp only [Pi.neg_apply,he]
  split_ifs <;> (try omega) <;> push_cast <;> ring

theorem series_conjugate {d : ℕ} (a : Frequency d → ℂ) (x : Torus d) :
    conj (absoluteFourierSeries a x)=
      absoluteFourierSeries (fun k => conj (a (-k))) x := by
  unfold absoluteFourierSeries
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k,conj (a (-k)*UnitAddTorus.mFourier (-k) x) :=
      ((Equiv.neg (Frequency d)).tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [map_mul,UnitAddTorus.mFourier_neg]
      simp

theorem halfSpectrum_real_part {d : ℕ} (i : Fin d) (l : Frequency d → ℝ)
    (hl : Summable (fun k => ‖l k‖)) (he : ∀ k,l (-k)=l k) (x : Torus d) :
    2*(absoluteFourierSeries (halfSpectrum i l) x).re=
      (absoluteFourierSeries (fun k => (l k:ℂ)) x).re := by
  have ha := halfSpectrum_summable i l hl
  have hb : Summable (fun k => ‖halfSpectrum i l (-k)‖) :=
    (Equiv.neg (Frequency d)).summable_iff.mpr ha
  have hsa : Summable (fun k => halfSpectrum i l k*UnitAddTorus.mFourier k x) := by
    apply ha.of_norm_bounded
    intro k; simp only [norm_mul,mFourier_norm_apply,mul_one,le_refl]
  have hsb : Summable (fun k => halfSpectrum i l (-k)*UnitAddTorus.mFourier k x) := by
    apply hb.of_norm_bounded
    intro k; simp only [norm_mul,mFourier_norm_apply,mul_one,le_refl]
  have hsum : absoluteFourierSeries (halfSpectrum i l) x+
      conj (absoluteFourierSeries (halfSpectrum i l) x)=
      absoluteFourierSeries (fun k => (l k:ℂ)) x := by
    rw [series_conjugate]
    simp_rw [halfSpectrum_real]
    unfold absoluteFourierSeries
    rw [← hsa.tsum_add hsb]
    apply tsum_congr
    intro k
    rw [← add_mul,halfSpectrum_pair i l he]
  have h := congrArg Complex.re hsum
  simp only [Complex.add_re,Complex.conj_re] at h
  linarith

theorem exponential_boundary_square {d : ℕ} (i : Fin d) (l : Frequency d → ℝ)
    (hl : Summable (fun k => ‖l k‖)) (he : ∀ k,l (-k)=l k) (x : Torus d) :
    Complex.normSq (Complex.exp (absoluteFourierSeries (halfSpectrum i l) x))=
      Real.exp ((absoluteFourierSeries (fun k => (l k:ℂ)) x).re) := by
  rw [← Complex.sq_norm,Complex.norm_exp,← Real.exp_nat_mul]
  congr 1
  exact halfSpectrum_real_part i l hl he x

#print axioms exponential_boundary_square
end BecknerOnofri.HighDim.CircleOuter
