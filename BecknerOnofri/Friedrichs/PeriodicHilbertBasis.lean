import BecknerOnofri.Friedrichs.PeriodicOrthogonality
import BecknerOnofri.Friedrichs.MixedCoordinateTotality

/-! A real Hilbert basis on the full unscaled Lebesgue circle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace BecknerOnofri.Friedrichs.PeriodicBasis

abbrev Index := ℕ ⊕ ℕ
abbrev measure : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))

def rawFunction : Index → ℝ → ℝ
  | .inl n => periodicMode false n
  | .inr n => periodicMode true (n+1)

def normSquared (i : Index) : ℝ := if i=Sum.inl 0 then 2*Real.pi else Real.pi

lemma normSquared_pos (i : Index) : 0<normSquared i := by
  unfold normSquared
  split_ifs <;> positivity

lemma rawFunction_memLp (i : Index) : MemLp (rawFunction i) 2 measure := by
  apply MemLp.of_bound (by cases i <;> exact (periodicMode_smooth _ _).continuous.aestronglyMeasurable) 1
  apply ae_of_all
  intro t
  cases i with
  | inl n => exact Real.abs_cos_le_one _
  | inr n => exact Real.abs_sin_le_one _

def rawVector (i : Index) : PeriodicRealL2 := (rawFunction_memLp i).toLp (rawFunction i)

lemma rawVector_inner (i j : Index) :
    inner ℝ (rawVector i) (rawVector j)=∫ t,rawFunction i t*rawFunction j t ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(rawFunction_memLp i).coeFn_toLp,(rawFunction_memLp j).coeFn_toLp] with t hi hj
  simp only [rawVector,hi,hj,RCLike.inner_apply,conj_trivial]
  ring

lemma rawVector_inner_self (i : Index) : inner ℝ (rawVector i) (rawVector i)=normSquared i := by
  rw [rawVector_inner]
  cases i with
  | inl n =>
    have h := periodic_cos_cos_integral (n:ℤ) (n:ℤ)
    by_cases hn : n=0
    · subst n
      simpa [rawFunction,periodicMode,normSquared] using h
    · have hnn : (n:ℤ)+(n:ℤ)≠0 := by omega
      simpa [rawFunction,periodicMode,normSquared,hn,hnn] using h
  | inr n =>
    have h := periodic_sin_sin_integral ((n+1:ℕ):ℤ) ((n+1:ℕ):ℤ)
    have hnn : ((n+1:ℕ):ℤ)+((n+1:ℕ):ℤ)≠0 := by omega
    rw [if_neg hnn] at h
    simpa [rawFunction,periodicMode,normSquared] using h

lemma rawVector_orthogonal {i j : Index} (hij : i≠j) : inner ℝ (rawVector i) (rawVector j)=0 := by
  rw [rawVector_inner]
  cases i with
  | inl n =>
    cases j with
    | inl m =>
      have hnm : (n:ℤ)-(m:ℤ)≠0 := by intro he; apply hij; congr 1; omega
      have hnp : (n:ℤ)+(m:ℤ)≠0 := by intro he; apply hij; congr 1; omega
      simpa [rawFunction,periodicMode,hnm,hnp] using periodic_cos_cos_integral (n:ℤ) (m:ℤ)
    | inr m => simpa [rawFunction,periodicMode] using periodic_cos_sin_integral (n:ℤ) ((m+1:ℕ):ℤ)
  | inr n =>
    cases j with
    | inl m =>
      simpa [rawFunction,periodicMode,measure,mul_comm] using periodic_cos_sin_integral (m:ℤ) ((n+1:ℕ):ℤ)
    | inr m =>
      have hnm : ((n+1:ℕ):ℤ)-((m+1:ℕ):ℤ)≠0 := by intro he; apply hij; congr 1; omega
      have hnp : ((n+1:ℕ):ℤ)+((m+1:ℕ):ℤ)≠0 := by omega
      have he := periodic_sin_sin_integral ((n+1:ℕ):ℤ) ((m+1:ℕ):ℤ)
      rw [if_neg hnm,if_neg hnp] at he
      simpa [rawFunction,periodicMode] using he

def normalizedVector (i : Index) : PeriodicRealL2 := (Real.sqrt (normSquared i))⁻¹ • rawVector i

lemma normalizedVector_orthonormal : Orthonormal ℝ normalizedVector := by
  rw [orthonormal_iff_ite]
  intro i j
  split_ifs with h
  · subst j
    rw [normalizedVector,inner_smul_left,inner_smul_right,rawVector_inner_self]
    simp only [conj_trivial]
    have hs := Real.sq_sqrt (normSquared_pos i).le
    have hn := ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos i))
    field_simp
    nlinarith
  · rw [normalizedVector,normalizedVector,inner_smul_left,inner_smul_right,rawVector_orthogonal h]
    simp

lemma total (f : PeriodicRealL2) (h : ∀ i,inner ℝ f (normalizedVector i)=0) : f=0 := by
  have hr (i : Index) : inner ℝ f (rawVector i)=0 := by
    have hi := h i
    rw [normalizedVector,inner_smul_right] at hi
    exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (normSquared_pos i))))
  have hi (i : Index) : (∫ t,rawFunction i t*f t ∂measure)=0 := by
    have hr_i := hr i
    rw [L2.inner_def] at hr_i
    calc
      _ = ∫ t,inner ℝ (f t) (rawVector i t) ∂measure := by
        apply integral_congr_ae
        filter_upwards [(rawFunction_memLp i).coeFn_toLp] with t ht
        simp only [rawVector,ht,RCLike.inner_apply,conj_trivial]
      _ = 0 := hr_i
  apply MixedSpatial.periodic_modes_total f
  intro odd n
  cases odd
  · exact hi (.inl n)
  · cases n with
    | zero => simp [periodicMode]
    | succ n => exact hi (.inr n)

lemma orthogonalComplement : (Submodule.span ℝ (range normalizedVector))ᗮ=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply total f
  intro i
  exact Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self i)) hf

def hilbertBasis : HilbertBasis Index ℝ PeriodicRealL2 :=
  HilbertBasis.mkOfOrthogonalEqBot normalizedVector_orthonormal orthogonalComplement

@[simp] lemma hilbertBasis_apply (i : Index) : hilbertBasis i=normalizedVector i :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

#print axioms hilbertBasis
end BecknerOnofri.Friedrichs.PeriodicBasis
