module

public import Legacy.BecknerOnofri.ExponentialWordSeries
public import Legacy.BecknerOnofri.CircleMilinWords
public import Legacy.BecknerOnofri.CircleEqualitySeries

@[expose] public section

/-! The actual absolutely convergent word expansion of the circle exponential. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleMilin
open Legacy.TorusEndpoint ExponentialWordSeries

private theorem word_zero {K : Type*} [RCLike K] (a : ℕ → K) (ha0 : a 0 = 0)
    (xs : List ℕ) (hx : ¬ ∀ j ∈ xs, 0 < j) : word a xs = 0 := by
  have hz : 0 ∈ xs := by
    by_contra hh
    apply hx
    intro j hj
    exact Nat.pos_of_ne_zero (fun h => hh (h ▸ hj))
  have hm : (0 : K) ∈ xs.map a := List.mem_map.mpr ⟨0,hz,ha0⟩
  rw [word, List.prod_eq_zero_iff.mpr hm, mul_zero]

private theorem fiber_word_sum {K : Type*} [RCLike K] (a : ℕ → K)
    (ha0 : a 0 = 0) (n : ℕ) :
    (∑' xs : List.sum ⁻¹' {n}, word a xs) = ∑ xs ∈ words n, word a xs := by
  classical
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := words n) ?_]
  · apply Finset.sum_congr rfl
    intro xs hx
    exact Set.indicator_of_mem (s := List.sum ⁻¹' {n}) ((mem_words_iff n xs).mp hx).2 (word a)
  · intro xs hx
    by_cases hs : xs.sum = n
    · rw [Set.indicator_of_mem (s := List.sum ⁻¹' {n}) hs]
      exact word_zero a ha0 xs (fun hp => hx ((mem_words_iff n xs).mpr ⟨hp,hs⟩))
    · exact Set.indicator_of_notMem (s := List.sum ⁻¹' {n}) hs (word a)

theorem bCoeff_fiber (a : ℕ → ℂ) (ha0 : a 0 = 0) (n : ℕ) :
    bCoeff a n = ∑' xs : List.sum ⁻¹' {n}, complexWord a xs :=
  (fiber_word_sum a ha0 n).symm

theorem pCoeff_fiber (a : ℕ → ℂ) (n : ℕ) :
    pCoeff a n = ∑' xs : List.sum ⁻¹' {n}, pWord a xs := by
  exact (fiber_word_sum (fun j : ℕ => (j : ℝ)*‖a j‖^2) (by simp) n).symm

theorem bCoeff_summable (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun j => ‖a j‖)) : Summable (fun n => ‖bCoeff a n‖) := by
  have hs := word_norm_summable a ha
  have hb := hs.hasSum.tsum_fiberwise List.sum
  apply hb.summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [bCoeff_fiber a ha0]
  exact norm_tsum_le_tsum_norm (hs.subtype _)

theorem pCoeff_hasSum (a : ℕ → ℂ)
    (ha : Summable (fun j : ℕ => (j : ℝ)*‖a j‖^2)) :
    HasSum (pCoeff a) (Real.exp (∑' j : ℕ, (j : ℝ)*‖a j‖^2)) := by
  have hn : Summable (fun j : ℕ => ‖(j : ℝ)*‖a j‖^2‖) := by
    exact ha.norm
  have hs := (word_norm_summable (fun j : ℕ => (j : ℝ)*‖a j‖^2) hn).of_norm.hasSum
  rw [real_word_sum _ hn] at hs
  have he : pCoeff a = (fun n => ∑' xs : List.sum ⁻¹' {n}, word (fun j : ℕ => (j : ℝ)*‖a j‖^2) xs) :=
    funext (fun n => pCoeff_fiber a n)
  rw [he]
  exact hs.tsum_fiberwise List.sum

def analyticSeries (a : ℕ → ℂ) (x : Torus 1) : ℂ :=
  ∑' n : ℕ, a n * CircleEquality.character x ^ n

def fullExponentialCoefficient (a : ℕ → ℂ) : Frequency 1 → ℂ :=
  WienerFourier.grouped (complexWord a) (fun xs => CircleEquality.frequency (xs.sum : ℤ))

theorem fullExponentialCoefficient_summable (a : ℕ → ℂ)
    (ha : Summable (fun j => ‖a j‖)) : Summable (fun k => ‖fullExponentialCoefficient a k‖) :=
  WienerFourier.grouped_norm_summable _ _ (word_norm_summable a ha)

private theorem word_twist (a : ℕ → ℂ) (z : ℂ) (xs : List ℕ) :
    word (fun j => a j*z^j) xs = complexWord a xs*z^xs.sum := by
  have hh : (xs.map (fun j => a j*z^j)).prod = (xs.map a).prod*z^xs.sum := by
    induction xs with
    | nil => simp
    | cons j xs ih => simp only [List.map_cons,List.prod_cons,List.sum_cons,ih,pow_add]; ring
  simp only [word,complexWord,hh,mul_assoc]

theorem exponential_series (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) (x : Torus 1) :
    absoluteFourierSeries (fullExponentialCoefficient a) x = Complex.exp (analyticSeries a x) := by
  have ht : Summable (fun j => ‖a j*CircleEquality.character x^j‖) := by
    simpa only [norm_mul,norm_pow,CircleEquality.character_norm,one_pow,mul_one] using ha
  have hw : Summable (fun xs => ‖complexWord a xs‖) := word_norm_summable a ha
  rw [fullExponentialCoefficient,WienerFourier.grouped_series _ _ hw]
  change _ = Complex.exp (∑' n, a n*CircleEquality.character x^n)
  rw [← complex_word_sum _ ht]
  apply tsum_congr
  intro xs
  rw [word_twist,CircleEquality.character_pow]

theorem exponential_fourier (a : ℕ → ℂ) (ha : Summable (fun j => ‖a j‖)) (k : Frequency 1) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (analyticSeries a x)) k =
      fullExponentialCoefficient a k := by
  have hh : (fun x => Complex.exp (analyticSeries a x)) =
      absoluteFourierSeries (fullExponentialCoefficient a) := funext (fun x => (exponential_series a ha x).symm)
  rw [hh]
  exact absoluteFourierSeries_coefficient _ (fullExponentialCoefficient_summable a ha) k

theorem fullExponentialCoefficient_nat (a : ℕ → ℂ) (ha0 : a 0 = 0) (n : ℕ) :
    fullExponentialCoefficient a (CircleEquality.frequency n) = bCoeff a n := by
  have hh : (fun xs : List ℕ => CircleEquality.frequency (xs.sum : ℤ)) ⁻¹' {CircleEquality.frequency n} =
      List.sum ⁻¹' {n} := by
    ext xs
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      exact Int.ofNat.inj (congrFun h 0)
    · intro h
      rw [h]
  rw [fullExponentialCoefficient,WienerFourier.grouped,hh,← bCoeff_fiber a ha0]

theorem fullExponentialCoefficient_negative (a : ℕ → ℂ) (n : ℕ) :
    fullExponentialCoefficient a (CircleEquality.frequency (-(n+1 : ℤ))) = 0 := by
  have hh : (fun xs : List ℕ => CircleEquality.frequency (xs.sum : ℤ)) ⁻¹' {CircleEquality.frequency (-(n+1 : ℤ))} = ∅ := by
    ext xs
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    intro h
    have he := congrFun h 0
    simp only [CircleEquality.frequency_apply] at he
    omega
  rw [fullExponentialCoefficient,WienerFourier.grouped,hh]
  exact tsum_empty

theorem exponential_fourier_nat (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : Summable (fun j => ‖a j‖)) (n : ℕ) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (analyticSeries a x)) (CircleEquality.frequency n) = bCoeff a n := by
  rw [exponential_fourier a ha,fullExponentialCoefficient_nat a ha0]

theorem exponential_fourier_negative (a : ℕ → ℂ)
    (ha : Summable (fun j => ‖a j‖)) (n : ℕ) :
    UnitAddTorus.mFourierCoeff (fun x => Complex.exp (analyticSeries a x)) (CircleEquality.frequency (-(n+1 : ℤ))) = 0 := by
  rw [exponential_fourier a ha,fullExponentialCoefficient_negative]

#print axioms bCoeff_summable
#print axioms pCoeff_hasSum
#print axioms exponential_fourier_nat
#print axioms exponential_fourier_negative
end Legacy.BecknerOnofri.CircleMilin
