module

public import Legacy.BecknerOnofri.SpectralHeatInverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Finite spectral truncation in operator norm proves actual inverse-power compactness. -/
noncomputable section
open Set Filter Classical
open scoped Topology BigOperators ENNReal
namespace Legacy.BecknerOnofri.SpectralHeatInverse
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual finite-rank sum of the rank-one spectral operators. -/
def finiteOperator (e : HilbertBasis ι ℝ H) (a : Symbol ι) (F : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ F, (coordinate e i).smulRight (a i • e i)

@[simp] theorem coordinate_basis (e : HilbertBasis ι ℝ H) (i j : ι) :
    coordinate e i (e j) = if i=j then 1 else 0 := by
  classical
  rw [coordinate_apply,e.repr_self,lp.single_apply]
  simp [Pi.single_apply,eq_comm]

theorem coordinate_finiteOperator (e : HilbertBasis ι ℝ H) (a : Symbol ι)
    (F : Finset ι) (u : H) (i : ι) :
    coordinate e i (finiteOperator e a F u) = if i∈F then a i*coordinate e i u else 0 := by
  classical
  simp [finiteOperator,ContinuousLinearMap.sum_apply,map_sum,coordinate_basis,
    map_smul, e.repr_self, lp.single_apply, Pi.single_apply, mul_comm]

def truncateSymbol (a : Symbol ι) (F : Finset ι) : Symbol ι := by
  classical
  exact boundedSymbol (fun i => if i∈F then a i else 0) ‖a‖ (by
    intro i
    split_ifs
    · exact lp.norm_apply_le_norm ENNReal.top_ne_zero a i
    · simpa using norm_nonneg a)

theorem finiteOperator_eq_diagonal (e : HilbertBasis ι ℝ H) (a : Symbol ι)
    (F : Finset ι) : finiteOperator e a F = diagonal e (truncateSymbol a F) := by
  classical
  ext u
  apply ext_coordinates e
  intro i
  rw [coordinate_finiteOperator]
  simp only [coordinate_apply,repr_diagonal]
  change (if i∈F then a i*e.repr u i else 0) = (if i∈F then a i else 0)*e.repr u i
  split_ifs <;> simp

theorem finiteOperator_compact (e : HilbertBasis ι ℝ H) (a : Symbol ι)
    (F : Finset ι) : IsCompactOperator (finiteOperator e a F) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    change IsCompactOperator (0 : H →L[ℝ] H)
    convert! (isCompactOperator_zero : IsCompactOperator (fun _ : H => (0:H))) using 1
  | @insert i F hi hF =>
    have hi' : IsCompactOperator ((coordinate e i).smulRight (a i • e i)) := by
      exact (isCompactOperator_of_locallyCompactSpace_dom (coordinate e i)).clm_comp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (a i • e i))
    simp only [finiteOperator,Finset.sum_insert hi]
    convert! hi'.add hF using 1

/-- Finite spectral sublevel sets, with no ordering or countability of the basis index assumed. -/
def spectralCutoff (D : PositiveSpectrum ι)
    (hfinite : ∀ R : ℝ, {i | D.value i ≤ R}.Finite) (n : ℕ) : Finset ι :=
  (hfinite ((n:ℝ)+1)).toFinset

@[simp] theorem mem_spectralCutoff (D : PositiveSpectrum ι)
    (hfinite : ∀ R : ℝ, {i | D.value i ≤ R}.Finite) (n : ℕ) (i : ι) :
    i∈spectralCutoff D hfinite n ↔ D.value i ≤ (n:ℝ)+1 := by
  simp [spectralCutoff]

theorem inversePower_truncation_error (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (hfinite : ∀ R : ℝ, {i | D.value i ≤ R}.Finite) (s : ℝ) (hs : 0<s) (n : ℕ) :
    ‖inversePower e D s hs - finiteOperator e (D.inverseSymbol s hs) (spectralCutoff D hfinite n)‖
      ≤ ((n:ℝ)+1)^(-s) := by
  classical
  rw [finiteOperator_eq_diagonal,inversePower,← diagonal_sub]
  apply diagonal_norm_le e _ (Real.rpow_nonneg (by positivity) _)
  intro i
  change ‖D.value i^(-s) - (if i∈spectralCutoff D hfinite n then D.value i^(-s) else 0)‖ ≤ _
  split_ifs with hi
  · simp only [sub_self,norm_zero]
    positivity
  · rw [sub_zero,Real.norm_of_nonneg (Real.rpow_nonneg (D.value_pos i).le _)]
    have hh : (n:ℝ)+1 ≤ D.value i := (not_le.mp (by simpa using hi)).le
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hh (by linarith)

theorem inversePower_truncation_tendsto (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (hfinite : ∀ R : ℝ, {i | D.value i ≤ R}.Finite) (s : ℝ) (hs : 0<s) :
    Tendsto (fun n : ℕ => finiteOperator e (D.inverseSymbol s hs) (spectralCutoff D hfinite n))
      atTop (𝓝 (inversePower e D s hs)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => (norm_sub_rev _ _).le.trans (inversePower_truncation_error e D hfinite s hs n))
  exact (tendsto_rpow_neg_atTop hs).comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)

/-- A positive-gap spectrum with finite sublevels has compact actual negative powers. -/
theorem inversePower_compact (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (hfinite : ∀ R : ℝ, {i | D.value i ≤ R}.Finite) (s : ℝ) (hs : 0<s) :
    IsCompactOperator (inversePower e D s hs) := by
  exact isCompactOperator_of_tendsto (inversePower_truncation_tendsto e D hfinite s hs)
    (Eventually.of_forall fun _ => finiteOperator_compact e _ _)

#print axioms inversePower_truncation_tendsto
#print axioms inversePower_compact
end Legacy.BecknerOnofri.SpectralHeatInverse
