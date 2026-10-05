import BecknerOnofri.SelectedNumericalModel

/-! Nonnegative Fourier exponentiation forces additive closure of the
support at an actual Euler stationary point. Only its quadratic Taylor
term is needed for closure under addition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.PositiveFourierSupport
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler

theorem convolution_ofReal {d : ℕ} (a b : Frequency d → ℝ) (k : Frequency d) :
    WienerFourier.convolution (fun j => (a j : ℂ)) (fun j => (b j : ℂ)) k=
      (fourierConvolution a b k : ℂ) := by
  simp only [WienerFourier.convolution,WienerFourier.grouped,fourierConvolution,
    groupedFourierCoefficients,Complex.ofReal_tsum,Complex.ofReal_mul]

theorem convolutionPower_ofReal {d : ℕ} (a : Frequency d → ℝ) (n : ℕ) (k : Frequency d) :
    WienerFourier.convolutionPower (fun j => (a j : ℂ)) n k=(fourierPower a n k : ℂ) := by
  classical
  induction n generalizing k with
  | zero => simp only [WienerFourier.convolutionPower,fourierPower]; split_ifs <;> norm_num
  | succ n ih =>
    rw [WienerFourier.convolutionPower,fourierPower,funext ih]
    exact convolution_ofReal _ _ _

theorem exponentialCoefficients_ofReal {d : ℕ} (a : Frequency d → ℝ) (k : Frequency d) :
    WienerFourier.exponentialCoefficients (fun j => (a j : ℂ)) k=(fourierExponential a k : ℂ) := by
  simp only [WienerFourier.exponentialCoefficients,fourierExponential,convolutionPower_ofReal,
    Complex.ofReal_tsum,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast]

theorem fourierPower_one {d : ℕ} (a : Frequency d → ℝ) (k : Frequency d) : fourierPower a 1 k=a k := by
  classical
  unfold fourierPower fourierConvolution groupedFourierCoefficients
  let j : (fun p : Frequency d×Frequency d => p.1+p.2) ⁻¹' {k} := ⟨(0,k),by simp⟩
  rw [tsum_eq_single j]
  · simp [j,fourierPower]
  · intro p hp
    by_cases hp0 : p.val.1=0
    · have hp2 : p.val.2=k := by simpa only [Set.mem_preimage,Set.mem_singleton_iff,hp0,zero_add] using p.property
      have he : p=j := Subtype.ext (Prod.ext hp0 hp2)
      exact False.elim (hp he)
    · simp [fourierPower,hp0]

theorem fourierExponential_add_pos {d : ℕ} (a : Frequency d → ℝ)
    (ha : ∀ k,0≤a k) (hs : Summable a) {k l : Frequency d} (hk : 0<a k) (hl : 0<a l) :
    0<fourierExponential a (k+l) := by
  classical
  have hc : 0<fourierConvolution a a (k+l) := by
    have ht := (hs.mul_of_nonneg hs ha ha).subtype (fun p : Frequency d×Frequency d => p.1+p.2=k+l)
    exact ht.tsum_pos (fun p => mul_nonneg (ha p.val.1) (ha p.val.2))
      ⟨(k,l),rfl⟩ (mul_pos hk hl)
  have hp : 0<fourierPower a 2 (k+l) := by
    change 0<fourierConvolution (fourierPower a 1) a (k+l)
    rw [show fourierPower a 1=a from funext (fourierPower_one a)]
    exact hc
  exact ((fourierExponential_joint_summable a hs ha).prod_symm.prod_factor (k+l)).tsum_pos
    (fun n => mul_nonneg (by positivity) (fourierPower_nonneg a ha n (k+l))) 2
    (mul_pos (by positivity) hp)

/-- The algebraic closure statement used after the actual Euler equation
identifies every nonzero exponential support mode with a potential mode. -/
def supportGroup {d : ℕ} (a : Frequency d → ℝ) (ha : ∀ k,0≤a k) (hs : Summable a)
    (heven : ∀ k,a (-k)=a k)
    (hEuler : ∀ k,k≠0 → 0<fourierExponential a k → 0<a k) : AddSubgroup (Frequency d) where
  carrier := {k | k=0 ∨ 0<a k}
  zero_mem' := Or.inl rfl
  neg_mem' := by
    intro k hk
    rcases hk with rfl | hk
    · exact Or.inl neg_zero
    · exact Or.inr (by rwa [heven])
  add_mem' := by
    intro k l hk hl
    change k+l=0 ∨ 0<a (k+l)
    change k=0 ∨ 0<a k at hk
    change l=0 ∨ 0<a l at hl
    rcases hk with rfl | hk
    · simpa only [zero_add] using hl
    rcases hl with rfl | hl
    · simpa only [add_zero] using (Or.inr hk : k=0 ∨ 0<a k)
    by_cases hkl : k+l=0
    · exact Or.inl hkl
    · exact Or.inr (hEuler _ hkl (fourierExponential_add_pos a ha hs hk hl))

open SelectedNumericalModel

theorem selected_density_exponential {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    densityFourier (gibbsValue u) k=(fourierExponential (amplitude u) k : ℂ)/(partition u : ℂ) := by
  have h := WienerFourier.normalized_real_exp_coefficient u (fourier_norm_summable hu) hu.1.1 (partition u) k
  change densityFourier (gibbsValue u) k=_ at h
  rw [show (fourierIsometry 12 u : Frequency 12 → ℂ)=(fun j => (amplitude u j : ℂ)) from
    funext (fourier_eq_amplitude hu),exponentialCoefficients_ofReal] at h
  exact h

theorem selected_amplitude_even {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    amplitude u (-k)=amplitude u k := by
  unfold amplitude
  rw [fourier_real_symmetry hu.1.1,Complex.conj_re]

theorem selected_support_euler {u : TorusL2 12} (hu : Selected u) (k : Frequency 12)
    (hk : k≠0) (hp : 0<fourierExponential (amplitude u) k) : 0<amplitude u k := by
  have h := congrArg Complex.re (maximizer_fourier_formula rough
    (by norm_num : (0:ℝ)<1/2) hu.1 hu.2.1 hk)
  rw [selected_density_exponential hu] at h
  simp only [show 1/(2*(1/2:ℝ))=1 by norm_num,one_mul,← Complex.ofReal_div,
    ← Complex.ofReal_mul,Complex.ofReal_re] at h
  change amplitude u k=_ at h
  rw [h]
  exact mul_pos (inv_pos.mpr (pow_pos (frequencyRadius_pos hk) _))
    (div_pos hp (SubcriticalAttainment.partition_pos rough hu.1))

/-- The genuine support of each selected maximizer, with zero adjoined, is
an additive subgroup of the integer frequency lattice. -/
def selectedSupportGroup (u : TorusL2 12) (hu : Selected u) : AddSubgroup (Frequency 12) :=
  supportGroup (amplitude u) (amplitude_nonneg hu) (amplitude_summable hu)
    (selected_amplitude_even hu) (selected_support_euler hu)

@[simp] theorem mem_selectedSupportGroup (u : TorusL2 12) (hu : Selected u) (k : Frequency 12) :
    k∈selectedSupportGroup u hu ↔ k=0 ∨ 0<amplitude u k := Iff.rfl

#print axioms fourierExponential_add_pos
#print axioms selectedSupportGroup
end BecknerOnofri.HighDim.PositiveFourierSupport
