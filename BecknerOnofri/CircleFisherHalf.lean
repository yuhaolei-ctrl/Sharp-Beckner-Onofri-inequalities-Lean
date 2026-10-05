module

public import BecknerOnofri.CircleTorusDerivative

@[expose] public section

/-! The |n| multiplier of a real even logarithm is twice the real part
of the signed multiplier of its one-sided half-spectrum. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleFisher
open Legacy.TorusEndpoint CircleOuter

theorem halfSpectrum_signed (l : Frequency 1 → ℝ) (k : Frequency 1) :
    halfSpectrum 0 (fun j => |(j (0:Fin 1):ℝ)| * l j) k=
      (k (0:Fin 1):ℂ)*halfSpectrum 0 l k := by
  unfold halfSpectrum
  split_ifs with h0 hp
  · simp [h0]
  · have hpos : 0<(k (0:Fin 1):ℝ) := by exact_mod_cast hp
    change ((|(k (0:Fin 1):ℝ)| * l k:ℝ):ℂ)=(k (0:Fin 1):ℂ)*(l k:ℂ)
    rw [abs_of_pos hpos]
    push_cast
    rfl
  · simp

theorem half_signed_real_part (l : Frequency 1 → ℝ)
    (hs : Summable (fun k => ‖|(k (0:Fin 1):ℝ)| * l k‖))
    (he : ∀ k,l (-k)=l k) (x : Torus 1) :
    2*(signedSeries (halfSpectrum 0 l) x).re=
      (absoluteFourierSeries (fun k => (|(k (0:Fin 1):ℝ)| * l k:ℝ)) x).re := by
  have hh : ∀ k, |((-k) (0:Fin 1):ℝ)| * l (-k)=|(k (0:Fin 1):ℝ)| * l k := by
    intro k
    simp only [Pi.neg_apply,Int.cast_neg,abs_neg,he]
  have h := halfSpectrum_real_part 0 (fun k => |(k (0:Fin 1):ℝ)| * l k) hs hh x
  simpa only [halfSpectrum_signed,absoluteFourierSeries,signedSeries] using h

theorem normSq_log_derivative (z w : ℂ) :
    Complex.normSq z*(2*w.re)=2*(conj z*(z*w)).re := by
  have h : conj z*(z*w)=(Complex.normSq z:ℂ)*w := by
    rw [← mul_assoc,← Complex.normSq_eq_conj_mul_self]
  rw [h]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

#print axioms half_signed_real_part
end BecknerOnofri.HighDim.CircleFisher
