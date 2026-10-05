module

public import BecknerOnofri.GreenHilbertContinuous
public import BecknerOnofri.RawComplementGap

@[expose] public section

/-! Exact omitted inverse-Fourier tails for the dimension-twelve enclosure
iteration. The tail constant is the genuine omitted lattice sum, and the
uniform estimate follows from Parseval and Cauchy--Schwarz. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Classical
open scoped BigOperators ENNReal ComplexConjugate
namespace BecknerOnofri.HighDim.IterationOmittedTail
open Legacy.BecknerOnofri.TorusSobolev

abbrev OmittedFrequency {d : ℕ} (A : Finset (Frequency d)) :=
  {k : Frequency d // k ≠ 0 ∧ k ∉ A}

def tailVector {d : ℕ} (A : Finset (Frequency d)) : FourierL2 d :=
  ⟨fun k => if k∈A then 0 else greenFourierVector d k,
    (lp.memℓp (greenFourierVector d)).mono' (fun k => by split_ifs <;> simp)⟩

@[simp] theorem tailVector_apply {d : ℕ} (A : Finset (Frequency d)) (k : Frequency d) :
    tailVector A k=if k∈A then 0 else greenFourierVector d k := rfl

/-- Exact C_A; the following theorem identifies its square with the lattice sum. -/
def tailConstant {d : ℕ} (A : Finset (Frequency d)) : ℝ := ‖tailVector A‖

theorem tailConstant_nonneg {d : ℕ} (A : Finset (Frequency d)) : 0≤tailConstant A := norm_nonneg _

theorem tailVector_omitted {d : ℕ} (hd : 0<d) (A : Finset (Frequency d)) (k : OmittedFrequency A) :
    tailVector A k.val=((1/frequencyLength k.val^d : ℝ):ℂ) := by
  rw [tailVector_apply,if_neg k.property.2,greenFourierVector_apply hd,if_neg k.property.1]

theorem tailVector_support {d : ℕ} (hd : 0<d) (A : Finset (Frequency d)) :
    Function.support (fun k => ‖tailVector A k‖^2) ⊆ {k | k≠0 ∧ k∉A} := by
  intro k hk
  have hne : tailVector A k≠0 := by
    intro he
    change ‖tailVector A k‖^2≠0 at hk
    rw [he] at hk
    norm_num at hk
  constructor
  · intro hk0
    subst k
    simp [tailVector_apply,greenFourierVector_apply hd] at hne
  · intro hkA
    simp [tailVector_apply,hkA] at hne

theorem tailVector_norm_sq {d : ℕ} (hd : 0<d) (A : Finset (Frequency d)) (k : OmittedFrequency A) :
    ‖tailVector A k.val‖^2=1/frequencyLength k.val^(2*d) := by
  rw [tailVector_omitted hd]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,one_pow,← pow_mul,Nat.mul_comm d 2]

/-- The exact omitted lattice sum is summable and equals C_A². -/
theorem tailConstant_hasSum {d : ℕ} (hd : 0<d) (A : Finset (Frequency d)) :
    HasSum (fun k : OmittedFrequency A => 1/frequencyLength k.val^(2*d)) ((tailConstant A)^2) := by
  have hs := lp.hasSum_norm (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) (tailVector A)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs
  have hsub := (hasSum_subtype_iff_of_support_subset (tailVector_support hd A)).mpr hs
  convert! hsub.congr_fun (fun k => (tailVector_norm_sq hd A k).symm) using 1

theorem tailConstant_sq {d : ℕ} (hd : 0<d) (A : Finset (Frequency d)) :
    (tailConstant A)^2=∑' k : OmittedFrequency A, 1/frequencyLength k.val^(2*d) :=
  (tailConstant_hasSum hd A).tsum_eq.symm

/-- The actual raw L² Fourier vector. -/
def fourierVector {d : ℕ} (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) : FourierL2 d :=
  fourierIsometry d (Bridge.potentialLp f hf)

@[simp] theorem fourierVector_apply {d : ℕ} (f : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (k : Frequency d) :
    fourierVector f hf k=fourierCoeff f k := Bridge.potentialLp_fourier f hf k

/-- Parseval identifies the norm on the right with the actual real L² norm. -/
theorem fourierVector_norm {d : ℕ} (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) :
    ‖fourierVector f hf‖=Real.sqrt (∫ x, (f x)^2 ∂torusMeasure d) := by
  have hs := lp.hasSum_norm (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) (fourierVector f hf)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,fourierVector_apply] at hs
  have he := hs.unique (RawComplementGap.raw_fourier_square_hasSum f hf)
  rw [← he,Real.sqrt_sq (norm_nonneg _)]

theorem tail_product_summable {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d) :
    Summable (fun k => ‖tailVector A k*a k‖) := by
  simp only [norm_mul]
  exact lp.summable_mul (by simpa using Real.HolderConjugate.two_two) (tailVector A) a

/-- Cauchy--Schwarz bounds the whole absolutely convergent omitted coefficient mass. -/
theorem tail_product_bound {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d) :
    (∑' k, ‖tailVector A k*a k‖)≤tailConstant A*‖a‖ := by
  simp only [norm_mul,tailConstant]
  exact lp.tsum_mul_le_mul_norm' (by simpa using Real.HolderConjugate.two_two) (tailVector A) a

/-- The actual omitted Fourier potential, as a uniformly controlled continuous series. -/
def omittedPotential {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d) : C(Torus d,ℂ) :=
  ⟨Legacy.TorusEndpoint.absoluteFourierSeries (fun k => tailVector A k*a k),
    Legacy.TorusEndpoint.absoluteFourierSeries_continuous _ (tail_product_summable A a)⟩

theorem omittedPotential_coefficient {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d)
    (k : Frequency d) : UnitAddTorus.mFourierCoeff (omittedPotential A a) k=tailVector A k*a k :=
  Legacy.TorusEndpoint.absoluteFourierSeries_coefficient _ (tail_product_summable A a) k

theorem omittedPotential_bound {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d) (x : Torus d) :
    ‖omittedPotential A a x‖≤tailConstant A*‖a‖ := by
  calc
    _ ≤ ∑' k, ‖tailVector A k*a k*UnitAddTorus.mFourier k x‖ :=
      norm_tsum_le_tsum_norm (Legacy.TorusEndpoint.summable_fourierSeries_apply _
        (tail_product_summable A a) x).norm
    _ = ∑' k, ‖tailVector A k*a k‖ := by
      simp only [norm_mul,Legacy.TorusEndpoint.mFourier_norm_apply,mul_one]
    _ ≤ _ := tail_product_bound A a

theorem omittedPotential_norm_le {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d) :
    ‖omittedPotential A a‖≤tailConstant A*‖a‖ :=
  (ContinuousMap.norm_le _ (mul_nonneg (tailConstant_nonneg A) (norm_nonneg _))).mpr
    (omittedPotential_bound A a)

theorem omittedPotential_raw_bound {d : ℕ} (A : Finset (Frequency d))
    (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) (x : Torus d) :
    ‖omittedPotential A (fourierVector f hf) x‖≤
      tailConstant A*Real.sqrt (∫ y, (f y)^2 ∂torusMeasure d) := by
  simpa only [fourierVector_norm] using omittedPotential_bound A (fourierVector f hf) x

theorem omitted_norm_hasSum {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) :
    HasSum (fun k : OmittedFrequency A => (1/frequencyLength k.val^d)*‖fourierCoeff f k.val‖)
      (∑' k, ‖tailVector A k*fourierVector f hf k‖) := by
  have hsupport : Function.support (fun k => ‖tailVector A k*fourierVector f hf k‖) ⊆
      {k | k≠0 ∧ k∉A} := by
    intro k hk
    apply tailVector_support hd A
    change ‖tailVector A k‖^2≠0
    intro hz
    have he : tailVector A k=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
    change ‖tailVector A k*fourierVector f hf k‖≠0 at hk
    rw [he,zero_mul,norm_zero] at hk
    exact hk rfl
  have hsub := (hasSum_subtype_iff_of_support_subset hsupport).mpr
    (tail_product_summable A (fourierVector f hf)).hasSum
  convert! hsub.congr_fun (fun k => ?_) using 1
  dsimp only [Function.comp_apply]
  rw [tailVector_omitted hd, norm_mul,fourierVector_apply,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by unfold frequencyLength; positivity : 0≤1/frequencyLength k.val^d)]

/-- Exact actual omitted Fourier mass, with no finite-frequency truncation of the tail. -/
theorem omitted_norm_bound {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) :
    (∑' k : OmittedFrequency A, (1/frequencyLength k.val^d)*‖fourierCoeff f k.val‖) ≤
      tailConstant A*Real.sqrt (∫ x, (f x)^2 ∂torusMeasure d) := by
  rw [(omitted_norm_hasSum hd A f hf).tsum_eq]
  simpa only [fourierVector_norm] using tail_product_bound A (fourierVector f hf)

theorem omitted_real_summable {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) :
    Summable (fun k : OmittedFrequency A => (1/frequencyLength k.val^d)*(fourierCoeff f k.val).re) := by
  apply (omitted_norm_hasSum hd A f hf).summable.of_norm_bounded
  intro k
  have hw : 0≤1/frequencyLength k.val^d := by unfold frequencyLength; positivity
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hw,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hw

/-- The source's real nonnegative-coefficient tail mass obeys the same sharp
Cauchy--Schwarz constant. The upper inequality even holds without coefficient signs. -/
theorem omitted_real_bound {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) :
    (∑' k : OmittedFrequency A, (1/frequencyLength k.val^d)*(fourierCoeff f k.val).re) ≤
      tailConstant A*Real.sqrt (∫ x, (f x)^2 ∂torusMeasure d) := by
  apply le_trans _ (omitted_norm_bound hd A f hf)
  apply Summable.tsum_le_tsum _ (omitted_real_summable hd A f hf) (omitted_norm_hasSum hd A f hf).summable
  intro k
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (Complex.abs_re_le_norm _))
    (by unfold frequencyLength; positivity)

theorem omitted_real_nonneg {d : ℕ} (A : Finset (Frequency d)) (f : Torus d → ℝ)
    (hpos : ∀ k : OmittedFrequency A, 0≤(fourierCoeff f k.val).re) :
    0≤∑' k : OmittedFrequency A, (1/frequencyLength k.val^d)*(fourierCoeff f k.val).re :=
  tsum_nonneg (fun k => mul_nonneg (by unfold frequencyLength; positivity) (hpos k))

/-- Direct enclosure-iteration interface: every genuine density norm bound M
implies the displayed omitted potential coefficient bound C_A M. -/
theorem density_omitted_bound {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (ρ : ProbabilityDensity d) (hρ : MemLp ρ.value 2 (torusMeasure d)) {M : ℝ}
    (hM : Real.sqrt (∫ x, (ρ.value x)^2 ∂torusMeasure d)≤M) :
    (∑' k : OmittedFrequency A, (1/frequencyLength k.val^d)*(fourierCoeff ρ.value k.val).re) ≤
      tailConstant A*M :=
  (omitted_real_bound hd A ρ.value hρ).trans (mul_le_mul_of_nonneg_left hM (tailConstant_nonneg A))

/-- The continuous tail is exactly the full actual inverse Fourier potential
minus its finite A-polynomial, pointwise at every torus point. -/
theorem omittedPotential_eq_sub_finite {d : ℕ} (A : Finset (Frequency d)) (a : FourierL2 d)
    (x : Torus d) :
    omittedPotential A a x=greenLiftComplex d a x-
      ∑ k∈A, greenFourierVector d k*a k*UnitAddTorus.mFourier k x := by
  have hs := Legacy.TorusEndpoint.summable_fourierSeries_apply _ (green_series_summable d a) x
  have hsum := hs.sum_add_tsum_compl (s := A)
  have ht : (∑' k : ↥((A : Set (Frequency d))ᶜ),
      greenFourierVector d k.val*a k.val*UnitAddTorus.mFourier k.val x)=omittedPotential A a x := by
    refine (tsum_subtype ((A : Set (Frequency d))ᶜ)
      (fun k => greenFourierVector d k*a k*UnitAddTorus.mFourier k x)).trans ?_
    apply tsum_congr
    intro k
    by_cases hk : k∈A
    · simp [Set.indicator,tailVector_apply,hk]
    · simp [Set.indicator,tailVector_apply,hk]
  rw [ht] at hsum
  change (∑ k∈A, greenFourierVector d k*a k*UnitAddTorus.mFourier k x)+omittedPotential A a x=
    greenLiftComplex d a x at hsum
  exact eq_sub_of_add_eq' hsum

/-- Real omitted potential; on symmetric A it is the real inverse Fourier tail. -/
def omittedRealPotential {d : ℕ} (A : Finset (Frequency d)) (f : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) : C(Torus d,ℝ) :=
  ⟨fun x => (omittedPotential A (fourierVector f hf) x).re,
    Complex.continuous_re.comp (omittedPotential A (fourierVector f hf)).continuous⟩

theorem omittedRealPotential_bound {d : ℕ} (A : Finset (Frequency d)) (f : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (x : Torus d) :
    |omittedRealPotential A f hf x|≤tailConstant A*Real.sqrt (∫ y, (f y)^2 ∂torusMeasure d) :=
  (Complex.abs_re_le_norm _).trans (omittedPotential_raw_bound A f hf x)

theorem tailVector_conjugate {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (hA : ∀ k, -k∈A ↔ k∈A) : ConjugateSymmetric (tailVector A : Frequency d → ℂ) := by
  intro k
  by_cases hk : k∈A
  · simp [tailVector_apply,hk,(hA k).mpr hk]
  · rw [tailVector_apply,tailVector_apply,if_neg hk,if_neg (show -k∉A from fun h => hk ((hA k).mp h))]
    exact greenFourierVector_conjugate hd k

theorem omittedPotential_real {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (hA : ∀ k, -k∈A ↔ k∈A) (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) (x : Torus d) :
    (omittedPotential A (fourierVector f hf) x).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  change conj (∑' k, (tailVector A k*fourierVector f hf k)*UnitAddTorus.mFourier k x)=_
  rw [Complex.conj_tsum]
  calc
    _ = ∑' k, (tailVector A (-k)*fourierVector f hf (-k))*UnitAddTorus.mFourier (-k) x := by
      apply tsum_congr
      intro k
      rw [map_mul,map_mul,tailVector_conjugate hd A hA k,fourierVector_apply,fourierVector_apply,
        fourierCoeff_conjugate f,UnitAddTorus.mFourier_neg]
    _ = _ := (Equiv.neg (Frequency d)).tsum_eq
      (fun k => (tailVector A k*fourierVector f hf k)*UnitAddTorus.mFourier k x)

theorem omittedRealPotential_fourier {d : ℕ} (hd : 0<d) (A : Finset (Frequency d))
    (hA : ∀ k, -k∈A ↔ k∈A) (f : Torus d → ℝ) (hf : MemLp f 2 (torusMeasure d)) (k : Frequency d) :
    fourierCoeff (omittedRealPotential A f hf) k=tailVector A k*fourierCoeff f k := by
  have he (x : Torus d) : ((omittedRealPotential A f hf x : ℝ):ℂ)=omittedPotential A (fourierVector f hf) x := by
    apply Complex.ext
    · rfl
    · exact (omittedPotential_real hd A hA f hf x).symm
  calc
    _ = UnitAddTorus.mFourierCoeff (omittedPotential A (fourierVector f hf)) k := by
      unfold fourierCoeff UnitAddTorus.mFourierCoeff
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [he]; rfl)
    _ = _ := by rw [omittedPotential_coefficient,fourierVector_apply]

#print axioms density_omitted_bound
#print axioms omittedPotential_eq_sub_finite
#print axioms omittedRealPotential_fourier
#print axioms tailConstant_sq
#print axioms omittedPotential_raw_bound
end BecknerOnofri.HighDim.IterationOmittedTail
