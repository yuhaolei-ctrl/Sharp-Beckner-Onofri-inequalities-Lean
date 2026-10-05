module

public import Legacy.BecknerOnofri.WienerFourier

@[expose] public section

/-! Exponentiation preserves absolutely summable Fourier coefficients with any
normalized submultiplicative weight.  The proof uses actual convolution fibers
and the explicit complex exponential coefficients from `WienerFourier`. -/

open scoped BigOperators

namespace Legacy.BecknerOnofri.WeightedWiener

open Legacy.TorusEndpoint WienerFourier

set_option maxHeartbeats 800000

structure IsWeight {d : ℕ} (w : Frequency d → ℝ) : Prop where
  one_le : ∀ k, 1 ≤ w k
  zero : w 0 = 1
  submul : ∀ k l, w (k + l) ≤ w k * w l

theorem IsWeight.nonneg {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w) (k) :
    0 ≤ w k := (by norm_num : (0 : ℝ) ≤ 1).trans (hw.one_le k)

theorem summable_norm {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    {a : Frequency d → ℂ} (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun k => ‖a k‖) :=
  ha.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (hw.one_le k))

theorem convolution_le {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a b : Frequency d → ℂ)
    (ha : Summable (fun k => w k * ‖a k‖))
    (hb : Summable (fun k => w k * ‖b k‖)) (k : Frequency d) :
    w k * ‖convolution a b k‖ ≤
      fourierConvolution (fun k => w k * ‖a k‖) (fun k => w k * ‖b k‖) k := by
  have ha' := summable_norm hw ha
  have hb' := summable_norm hw hb
  have hs := ha'.mul_of_nonneg hb' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hs' := ha.mul_of_nonneg hb
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
  calc
    _ ≤ w k * fourierConvolution (fun k => ‖a k‖) (fun k => ‖b k‖) k :=
      mul_le_mul_of_nonneg_left (convolution_norm_le a b ha' hb' k) (hw.nonneg k)
    _ = ∑' p : (fun p : Frequency d × Frequency d => p.1 + p.2) ⁻¹' {k},
        w k * (‖a p.val.1‖ * ‖b p.val.2‖) := by
      exact (tsum_mul_left).symm
    _ ≤ _ := by
      apply Summable.tsum_le_tsum _ ((hs.subtype _).mul_left (w k)) (hs'.subtype _)
      intro p
      change w k * (‖a p.val.1‖ * ‖b p.val.2‖) ≤
        (w p.val.1 * ‖a p.val.1‖) * (w p.val.2 * ‖b p.val.2‖)
      have hp : p.val.1 + p.val.2 = k := p.property
      calc
        _ = w (p.val.1 + p.val.2) * (‖a p.val.1‖ * ‖b p.val.2‖) := by rw [hp]
        _ ≤ (w p.val.1 * w p.val.2) * (‖a p.val.1‖ * ‖b p.val.2‖) :=
          mul_le_mul_of_nonneg_right (hw.submul _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = _ := by ring

theorem convolution_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a b : Frequency d → ℂ)
    (ha : Summable (fun k => w k * ‖a k‖))
    (hb : Summable (fun k => w k * ‖b k‖)) :
    Summable (fun k => w k * ‖convolution a b k‖) := by
  apply (fourierConvolution_hasSum _ _ ha hb
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))).summable.of_nonneg_of_le
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
  exact convolution_le hw a b ha hb

theorem power_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) (n) :
    Summable (fun k => w k * ‖convolutionPower a n k‖) := by
  classical
  induction n with
  | zero =>
    have he : (fun k => w k * ‖convolutionPower a 0 k‖) =
        fun k => if k = 0 then (1 : ℝ) else 0 := by
      funext k
      by_cases hk : k = 0 <;> simp [convolutionPower, hk, hw.zero]
    rw [he]
    exact (hasSum_ite_eq (0 : Frequency d) (1 : ℝ)).summable
  | succ n ih => exact convolution_summable hw _ _ ih ha

theorem power_le {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) (n k) :
    w k * ‖convolutionPower a n k‖ ≤ fourierPower (fun k => w k * ‖a k‖) n k := by
  classical
  have hpos (k) : 0 ≤ w k * ‖a k‖ := mul_nonneg (hw.nonneg k) (norm_nonneg _)
  induction n generalizing k with
  | zero =>
    by_cases hk : k = 0 <;> simp [convolutionPower, fourierPower, hk, hw.zero]
  | succ n ih =>
    exact (convolution_le hw _ _ (power_summable hw a ha n) ha k).trans
      (fourierConvolution_mono_left _ _ _ (power_summable hw a ha n)
        (fourierPower_hasSum _ ha hpos n).summable ha
        (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
        (fourierPower_nonneg _ hpos n) hpos ih k)

theorem exponential_joint_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun p : ℕ × Frequency d =>
      w p.2 * ‖(p.1.factorial : ℂ)⁻¹ * convolutionPower a p.1 p.2‖) := by
  apply (fourierExponential_joint_summable (fun k => w k * ‖a k‖) ha
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))).of_nonneg_of_le
    (fun p => mul_nonneg (hw.nonneg p.2) (norm_nonneg _))
  intro p
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ = (p.1.factorial : ℝ)⁻¹ * (w p.2 * ‖convolutionPower a p.1 p.2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (power_le hw a ha p.1 p.2) (by positivity)

theorem exponential_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun k => w k * ‖exponentialCoefficients a k‖) := by
  have hs := exponential_joint_summable hw a ha
  have hs0 := exponential_joint_norm_summable a (summable_norm hw ha)
  apply hs.prod_symm.prod.of_nonneg_of_le
    (fun k => mul_nonneg (hw.nonneg k) (norm_nonneg _))
  intro k
  calc
    _ ≤ w k * ∑' n, ‖(n.factorial : ℂ)⁻¹ * convolutionPower a n k‖ :=
      mul_le_mul_of_nonneg_left
        (norm_tsum_le_tsum_norm (hs0.prod_symm.prod_factor k)) (hw.nonneg k)
    _ = _ := (tsum_mul_left).symm

theorem exponential_fourier_summable {d : ℕ} {w : Frequency d → ℝ} (hw : IsWeight w)
    (a : Frequency d → ℂ) (ha : Summable (fun k => w k * ‖a k‖)) :
    Summable (fun k => w k *
      ‖UnitAddTorus.mFourierCoeff (fun x => Complex.exp (absoluteFourierSeries a x)) k‖) := by
  simpa only [exponential_coefficient a (summable_norm hw ha)] using exponential_summable hw a ha

#print axioms convolution_summable
#print axioms exponential_summable
#print axioms exponential_fourier_summable

end Legacy.BecknerOnofri.WeightedWiener
