module

public import Legacy.BecknerOnofri.SpectralDiagonal
public import Legacy.BecknerOnofri.GaussianMellinTerm
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Positive spectral data, genuine heat operators and the Bochner heat-integral inverse power.
No coordinate expansion, strong measurability, or integrability is assumed as an extra premise.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal
namespace Legacy.BecknerOnofri.SpectralHeatInverse

structure PositiveSpectrum (ι : Type*) where
  value : ι → ℝ
  gap : ℝ
  gap_pos : 0 < gap
  lower : ∀ i, gap ≤ value i

namespace PositiveSpectrum
variable {ι : Type*} (D : PositiveSpectrum ι)
theorem value_pos (i : ι) : 0 < D.value i := D.gap_pos.trans_le (D.lower i)

def heatSymbol (t : ℝ) : Symbol ι :=
  boundedSymbol (fun i => Real.exp (-(max t 0)*D.value i)) 1 (by
    intro i
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) (D.value_pos i).le)

def inverseSymbol (s : ℝ) (hs : 0 < s) : Symbol ι :=
  boundedSymbol (fun i => D.value i^(-s)) (D.gap^(-s)) (by
    intro i
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (D.value_pos i) _)]
    exact Real.rpow_le_rpow_of_nonpos D.gap_pos (D.lower i) (by linarith))
end PositiveSpectrum

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def heat (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) (t : ℝ) : H →L[ℝ] H :=
  diagonal e (D.heatSymbol t)

def inversePower (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) (s : ℝ) (hs : 0<s) : H →L[ℝ] H :=
  diagonal e (D.inverseSymbol s hs)

theorem repr_heat (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) {t : ℝ} (ht : 0≤t)
    (u : H) (i : ι) : e.repr (heat e D t u) i = Real.exp (-t*D.value i)*e.repr u i := by
  rw [heat,repr_diagonal]
  change Real.exp (-(max t 0)*D.value i)*e.repr u i = _
  rw [max_eq_left ht]

@[simp] theorem repr_inversePower (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (s : ℝ) (hs : 0<s) (u : H) (i : ι) :
    e.repr (inversePower e D s hs u) i = D.value i^(-s)*e.repr u i :=
  repr_diagonal e _ u i

theorem heat_symmetric (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) (t : ℝ) :
    (heat e D t).IsSymmetric := diagonal_symmetric e _

theorem inversePower_symmetric (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (s : ℝ) (hs : 0<s) : (inversePower e D s hs).IsSymmetric := diagonal_symmetric e _

theorem heat_norm_le (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) {t : ℝ} (ht : 0≤t) :
    ‖heat e D t‖ ≤ Real.exp (-D.gap*t) := by
  apply diagonal_norm_le e _ (Real.exp_nonneg _)
  intro i
  change ‖Real.exp (-(max t 0)*D.value i)‖ ≤ _
  rw [max_eq_left ht,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (D.lower i) ht
  nlinarith only [hh]

theorem heat_apply_norm_le (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    {t : ℝ} (ht : 0≤t) (u : H) : ‖heat e D t u‖ ≤ Real.exp (-D.gap*t)*‖u‖ :=
  ((heat e D t).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (heat_norm_le e D ht) (norm_nonneg u))

theorem inversePower_norm_le (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    (s : ℝ) (hs : 0<s) : ‖inversePower e D s hs‖ ≤ D.gap^(-s) := by
  apply diagonal_norm_le e _ (Real.rpow_pos_of_pos D.gap_pos _).le
  intro i
  change ‖D.value i^(-s)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (D.value_pos i) _)]
  exact Real.rpow_le_rpow_of_nonpos D.gap_pos (D.lower i) (by linarith)

/-- A scalar derivative bound uniform over all positive eigenvalues. -/
theorem scalar_derivative_bound {δ r : ℝ} (hδ : 0<δ) (hr : 0<r) :
    r*Real.exp (-δ*r) ≤ 1/δ := by
  have he := Real.add_one_le_exp (δ*r)
  have hh : (δ*r)*Real.exp (-δ*r) ≤ 1 := by
    calc
      _ ≤ Real.exp (δ*r)*Real.exp (-δ*r) :=
        mul_le_mul_of_nonneg_right (by linarith only [he]) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  apply (le_div_iff₀ hδ).mpr
  nlinarith only [hh]

theorem scalar_heat_lipschitz {δ r t u : ℝ} (hδ : 0<δ) (hr : 0<r)
    (ht : δ≤t) (hu : δ≤u) :
    ‖Real.exp (-t*r)-Real.exp (-u*r)‖ ≤ (1/δ)*‖t-u‖ := by
  have hd : ∀ v ∈ Ici δ, HasDerivWithinAt (fun z => Real.exp (-z*r))
      (-r*Real.exp (-v*r)) (Ici δ) v := by
    intro v hv
    convert! (((hasDerivAt_id v).neg.mul_const r).exp).hasDerivWithinAt using 1 <;>
      simp only [Pi.neg_apply,id_eq] <;> ring_nf
  have hb : ∀ v ∈ Ici δ, ‖-r*Real.exp (-v*r)‖ ≤ 1/δ := by
    intro v hv
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply le_trans _ (scalar_derivative_bound hδ hr)
    apply mul_le_mul_of_nonneg_left _ hr.le
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hv hr.le
    linarith
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici δ) hu ht

theorem heat_difference_norm_le (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    {δ t u : ℝ} (hδ : 0<δ) (ht : δ≤t) (hu : δ≤u) :
    ‖heat e D t-heat e D u‖ ≤ (1/δ)*‖t-u‖ := by
  rw [heat,heat,← diagonal_sub]
  apply diagonal_norm_le e _ (by positivity)
  intro i
  change ‖Real.exp (-(max t 0)*D.value i)-Real.exp (-(max u 0)*D.value i)‖ ≤ _
  rw [max_eq_left (hδ.le.trans ht),max_eq_left (hδ.le.trans hu)]
  exact scalar_heat_lipschitz hδ (D.value_pos i) ht hu

theorem continuousAt_heat (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    {t : ℝ} (ht : 0<t) : ContinuousAt (heat e D) t := by
  let C : ℝ≥0 := ⟨1/(t/2),by positivity⟩
  have hLip : LipschitzOnWith C (heat e D) (Ici (t/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [dist_eq_norm,dist_eq_norm]
    change ‖heat e D u-heat e D v‖ ≤ (1/(t/2))*‖u-v‖
    exact heat_difference_norm_le e D (by linarith : 0<t/2) hu hv
  exact (hLip.continuousOn t (by change t/2≤t; linarith)).continuousAt
    (Ici_mem_nhds (by linarith : t/2<t))

theorem continuousOn_heat_apply (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι) (u : H) :
    ContinuousOn (fun t => heat e D t u) (Ioi 0) := by
  intro t ht
  exact ((continuousAt_heat e D ht).clm_apply continuousAt_const).continuousWithinAt

/-- Genuine Bochner integrability follows from the spectral gap's scalar Gamma majorant. -/
theorem heat_integrable (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    {s : ℝ} (hs : 0<s) (u : H) :
    IntegrableOn (fun t : ℝ => t^(s-1) • heat e D t u) (Ioi 0) := by
  have hscalar : IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-D.gap*t)) (Ioi 0) := by
    convert! GaussianMellinTerm.shifted_integrable hs D.gap_pos 0 using 1
    funext t
    simp only [sub_zero]
    congr 2
    ring
  have hm : AEStronglyMeasurable (fun t : ℝ => t^(s-1) • heat e D t u)
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul _ (continuousOn_heat_apply e D u)
    intro t ht
    exact (Real.continuousAt_rpow_const t (s-1) (Or.inl (ne_of_gt ht))).continuousWithinAt
  apply (hscalar.mul_const ‖u‖).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  have hpow : 0 ≤ t^(s-1) := Real.rpow_nonneg ht0 (s-1)
  calc
    ‖t^(s-1) • heat e D t u‖ = t^(s-1)*‖heat e D t u‖ := by
      rw [norm_smul,Real.norm_of_nonneg hpow]
    _ ≤ t^(s-1)*Real.exp (-D.gap*t)*‖u‖ := by
      have hh := mul_le_mul_of_nonneg_left (heat_apply_norm_le e D ht0 u) hpow
      simpa only [mul_assoc] using hh

/-- The actual vector-valued heat integral equals the actual inverse-power multiplier. -/
theorem heat_integral_eq_inversePower (e : HilbertBasis ι ℝ H) (D : PositiveSpectrum ι)
    {s : ℝ} (hs : 0<s) (u : H) :
    (Real.Gamma s)⁻¹ • (∫ t : ℝ in Ioi 0, t^(s-1) • heat e D t u) = inversePower e D s hs u := by
  apply ext_coordinates e
  intro i
  rw [map_smul,← (coordinate e i).integral_comp_comm (heat_integrable e D hs u)]
  have he : (∫ t : ℝ in Ioi 0, coordinate e i (t^(s-1) • heat e D t u)) =
      (Real.Gamma s / D.value i^s)*e.repr u i := by
    calc
      _ = ∫ t : ℝ in Ioi 0, (t^(s-1)*Real.exp (-t*D.value i))*e.repr u i := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [map_smul,coordinate_apply,repr_heat e D ht.le]
        simp only [smul_eq_mul]
        ring
      _ = _ := by
        rw [integral_mul_const]
        have hh := GaussianMellinTerm.shifted_integral hs (D.value_pos i) 0
        simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using
          congrArg (fun r : ℝ => r*e.repr u i) hh
  rw [he,coordinate_apply,repr_inversePower,smul_eq_mul]
  rw [Real.rpow_neg (D.value_pos i).le]
  field_simp [(Real.Gamma_pos_of_pos hs).ne']

#print axioms heat_symmetric
#print axioms heat_apply_norm_le
#print axioms heat_integrable
#print axioms heat_integral_eq_inversePower
end Legacy.BecknerOnofri.SpectralHeatInverse
