module

public import BecknerOnofri.LocalElevenContinuousInverse
public import BecknerOnofri.QuarticSignsEleven
public import BecknerOnofri.FullHessianDecomposition
public import BecknerOnofri.LocalElevenCore.GraphHessianRaw

@[expose] public section

/-! Exact Hessian decomposition for every raw mean-zero critical-Sobolev
variation, with genuine weighted Fourier summability and polarization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.LocalEleven.FullHessianDecomposition

open BecknerOnofri.HighDim.FullHessianDecomposition hiding critical_add critical_sub fourierCoeff_add fourierCoeff_sub fourierCoeff_zero_of_meanZero graphComplement graphComplement_properties graph_decomposition normalizedEnergyPairing_summable normalizedEnergy_add rawCoordinates raw_sub_complement_supported reconstruction_meanZero reconstruction_rawCoordinates secondVariation_add secondVariation_congr_ae secondVariation_decomposition weighted_first_integrable weighted_pair_integrable
open BecknerOnofri.HighDim.GreenLocalBranch hiding correction correction_analytic correction_axis correction_base correction_derivative_zero correction_quadratic correction_solves correction_unique exists_analytic_complement green_assembly green_first_complement_zero linearPart_eq zero_axis_of_unique
open BecknerOnofri.HighDim.ReducedEquation hiding complementMap_assembly complementMap_reconstruction coordinates_complement coordinates_green coordinates_one coordinates_reconstruction full full_complement full_coordinates full_mean full_zero_iff graph_full_iff_reduced local_full_iff_reduced meanZero_zero_iff mean_green potential potential_analytic reduced reduced_analytic
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open BecknerOnofri.HighDim.GraphHessian hiding continuous_mul_raw_integrable differentiated_projected_equation hasFDerivAt_graphResidual hessianPairing hessianPairing_continuous hessianPairing_linearized_complement hessianPairing_linearized_raw_complement hessianPairing_raw hessianPairing_self hessianPairing_tangentMap_complement hessianPairing_tangentMap_raw_complement linearized_energy_term linearized_fourier_euler linearized_inCriticalSobolev linearized_normalizedEnergy linearized_pairing_complement linearized_pairing_raw_complement normalizedEnergyPairing normalizedEnergyPairing_self physical_factor raw_pairing_hasSum secondVariation_graph secondVariation_linearized secondVariation_tangentMap shell_residual_pairing tangentMap tangentMap_apply tangentMap_eq tangentMap_equation weighted_norm_pairing
open BecknerOnofri.HighDim.RawComplementGap hiding normalizedEnergy_gap normalizedEnergy_nonneg raw_fourier_square_hasSum raw_normalizedEnergy_hasSum
open GraphHessian RawComplementGap

open Legacy.BecknerOnofri.TorusSobolev

private theorem potentialLp_add {d : ℕ} (f g : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) :
    Bridge.potentialLp (f+g) (hf.add hg) = Bridge.potentialLp f hf+Bridge.potentialLp g hg := by
  apply Lp.ext
  filter_upwards [Bridge.potentialLp_ae (f+g) (hf.add hg),Bridge.potentialLp_ae f hf,
    Bridge.potentialLp_ae g hg,Lp.coeFn_add (Bridge.potentialLp f hf) (Bridge.potentialLp g hg)] with x hfg hfx hgx ha
  simp only [hfg,ha,Pi.add_apply,hfx,hgx,Complex.ofReal_add]

private theorem potentialLp_sub {d : ℕ} (f g : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) :
    Bridge.potentialLp (f-g) (hf.sub hg) = Bridge.potentialLp f hf-Bridge.potentialLp g hg := by
  apply Lp.ext
  filter_upwards [Bridge.potentialLp_ae (f-g) (hf.sub hg),Bridge.potentialLp_ae f hf,
    Bridge.potentialLp_ae g hg,Lp.coeFn_sub (Bridge.potentialLp f hf) (Bridge.potentialLp g hg)] with x hfg hfx hgx ha
  simp only [hfg,ha,Pi.sub_apply,hfx,hgx,Complex.ofReal_sub]

theorem fourierCoeff_add {d : ℕ} (f g : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) (k : Frequency d) :
    fourierCoeff (f+g) k = fourierCoeff f k+fourierCoeff g k := by
  rw [← Bridge.potentialLp_fourier (f+g) (hf.add hg),potentialLp_add f g hf hg,
    map_add,lp.coeFn_add,Pi.add_apply,Bridge.potentialLp_fourier,Bridge.potentialLp_fourier]

theorem fourierCoeff_sub {d : ℕ} (f g : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) (k : Frequency d) :
    fourierCoeff (f-g) k = fourierCoeff f k-fourierCoeff g k := by
  rw [← Bridge.potentialLp_fourier (f-g) (hf.sub hg),potentialLp_sub f g hf hg,
    map_sub,lp.coeFn_sub,Pi.sub_apply,Bridge.potentialLp_fourier,Bridge.potentialLp_fourier]

private theorem norm_add_square_le (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := norm_add_le a b
  nlinarith [norm_nonneg (a+b),norm_nonneg a,norm_nonneg b,sq_nonneg (‖a‖-‖b‖)]

private theorem norm_sub_square_le (a b : ℂ) : ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  simpa only [sub_eq_add_neg,norm_neg] using norm_add_square_le a (-b)

theorem critical_add {d : ℕ} (f g : Torus d → ℝ)
    (hf : InCriticalSobolev f) (hg : InCriticalSobolev g) : InCriticalSobolev (f+g) := by
  refine ⟨hf.1.add hg.1,?_⟩
  apply ((hf.2.add hg.2).mul_left 2).of_norm_bounded
  intro k
  have hw : 0 ≤ (2*Real.pi*frequencyLength k.val)^d := by unfold frequencyLength; positivity
  simp only [potentialTerm,fourierCoeff_add f g hf.1 hg.1,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  nlinarith [mul_le_mul_of_nonneg_left (norm_add_square_le (fourierCoeff f k.val) (fourierCoeff g k.val)) hw]

theorem critical_sub {d : ℕ} (f g : Torus d → ℝ)
    (hf : InCriticalSobolev f) (hg : InCriticalSobolev g) : InCriticalSobolev (f-g) := by
  refine ⟨hf.1.sub hg.1,?_⟩
  apply ((hf.2.add hg.2).mul_left 2).of_norm_bounded
  intro k
  have hw : 0 ≤ (2*Real.pi*frequencyLength k.val)^d := by unfold frequencyLength; positivity
  simp only [potentialTerm,fourierCoeff_sub f g hf.1 hg.1,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  nlinarith [mul_le_mul_of_nonneg_left (norm_sub_square_le (fourierCoeff f k.val) (fourierCoeff g k.val)) hw]

/-- Absolute summability of the actual energy cross term on the full lattice. -/
theorem normalizedEnergyPairing_summable {d : ℕ} (hd : 0<d) (f g : Torus d → ℝ)
    (hf : InCriticalSobolev f) (hg : InCriticalSobolev g) :
    Summable (fun k : Frequency d => frequencyLength k^d*(conj (fourierCoeff f k)*fourierCoeff g k).re) := by
  apply ((raw_normalizedEnergy_hasSum hd f hf).summable.add
    (raw_normalizedEnergy_hasSum hd g hg).summable).of_norm_bounded
  intro k
  have hw : 0 ≤ frequencyLength k^d := by unfold frequencyLength; positivity
  have hr : |(conj (fourierCoeff f k)*fourierCoeff g k).re| ≤
      ‖fourierCoeff f k‖*‖fourierCoeff g k‖ := by
    simpa only [norm_mul,Complex.norm_conj] using Complex.abs_re_le_norm (conj (fourierCoeff f k)*fourierCoeff g k)
  have hb : ‖fourierCoeff f k‖*‖fourierCoeff g k‖ ≤ ‖fourierCoeff f k‖^2+‖fourierCoeff g k‖^2 := by
    nlinarith [sq_nonneg (‖fourierCoeff f k‖-‖fourierCoeff g k‖),sq_nonneg ‖fourierCoeff f k‖,sq_nonneg ‖fourierCoeff g k‖]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg hw]
  nlinarith [mul_le_mul_of_nonneg_left (hr.trans hb) hw]

private theorem complex_norm_add_square (a b : ℂ) :
    ‖a+b‖^2=‖a‖^2+2*(conj a*b).re+‖b‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

/-- Exact polarization of the physical Fourier energy, justified by actual sums. -/
theorem normalizedEnergy_add {d : ℕ} (hd : 0<d) (f g : Torus d → ℝ)
    (hf : InCriticalSobolev f) (hg : InCriticalSobolev g) :
    normalizedPotentialEnergy (f+g)=normalizedPotentialEnergy f+
      2*normalizedEnergyPairing f g+normalizedPotentialEnergy g := by
  have hs := ((raw_normalizedEnergy_hasSum hd f hf).add
    ((normalizedEnergyPairing_summable hd f g hf hg).hasSum.mul_left 2)).add
      (raw_normalizedEnergy_hasSum hd g hg)
  apply (raw_normalizedEnergy_hasSum hd (f+g) (critical_add f g hf hg)).unique
  apply hs.congr_fun
  intro k
  rw [fourierCoeff_add f g hf.1 hg.1,complex_norm_add_square]
  ring

theorem weighted_pair_integrable {d : ℕ} (u : Space d) (f g : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) (hg : MemLp g 2 (torusMeasure d)) :
    Integrable (fun x => normalizedGibbs u x*f x*g x) (torusMeasure d) := by
  have hh := (hf.integrable_mul hg).bdd_mul (normalized u).continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => (normalized u).norm_coe_le_norm x))
  simpa only [normalized_apply,Pi.mul_apply,mul_assoc] using hh

theorem weighted_first_integrable {d : ℕ} (u : Space d) (f : Torus d → ℝ)
    (hf : MemLp f 2 (torusMeasure d)) :
    Integrable (fun x => normalizedGibbs u x*f x) (torusMeasure d) := by
  simpa only [normalized_apply] using continuous_mul_raw_integrable (normalized u) f hf

/-- Polarization of the actual physical second variation on raw functions. -/
theorem secondVariation_add {d : ℕ} (hd : 0<d) (β : ℝ) (u : Space d)
    (f g : Torus d → ℝ) (hf : InCriticalSobolev f) (hg : InCriticalSobolev g) :
    secondVariation β u (f+g)=secondVariation β u f+
      2*hessianPairing β u f g+secondVariation β u g := by
  have hmean : (∫ x, normalizedGibbs u x*(f+g) x ∂torusMeasure d) =
      (∫ x, normalizedGibbs u x*f x ∂torusMeasure d)+
      (∫ x, normalizedGibbs u x*g x ∂torusMeasure d) := by
    simp only [Pi.add_apply,mul_add]
    exact integral_add (weighted_first_integrable u f hf.1) (weighted_first_integrable u g hg.1)
  have hsquare : (∫ x, normalizedGibbs u x*((f+g) x)^2 ∂torusMeasure d) =
      (∫ x, normalizedGibbs u x*(f x)^2 ∂torusMeasure d)+
      2*(∫ x, normalizedGibbs u x*f x*g x ∂torusMeasure d)+
      (∫ x, normalizedGibbs u x*(g x)^2 ∂torusMeasure d) := by
    have he : (fun x => normalizedGibbs u x*((f+g) x)^2) =
        (fun x => (normalizedGibbs u x*(f x)^2+2*(normalizedGibbs u x*f x*g x))+
          normalizedGibbs u x*(g x)^2) := by funext x; simp only [Pi.add_apply]; ring
    have hs1 := integral_add (ComplementHessian.weighted_square_integrable u f hf.1)
      ((weighted_pair_integrable u f g hf.1 hg.1).const_mul 2)
    have hs2 := integral_add
      ((ComplementHessian.weighted_square_integrable u f hf.1).add
        ((weighted_pair_integrable u f g hf.1 hg.1).const_mul 2))
      (ComplementHessian.weighted_square_integrable u g hg.1)
    simp only [Pi.add_apply] at hs1 hs2
    rw [he,hs2,hs1,integral_const_mul]
  simp only [secondVariation,hsquare,hmean,normalizedEnergy_add hd f g hf hg,hessianPairing]
  ring

/-- The actual complex coordinates of a raw variation on the first shell. -/
def rawCoordinates {d : ℕ} (h : Torus d → ℝ) : Coordinates d :=
  fun i => fourierCoeff h (axisFrequency i)

/-- Remove the genuine graph tangent with the same first-shell coefficients. -/
def graphComplement {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d)
    (h : Torus d → ℝ) : Torus d → ℝ :=
  h-(tangentMap hd x (rawCoordinates h) : Torus d → ℝ)

theorem graph_decomposition {d : ℕ} (hd : 11 ≤ d) (x : ℝ × Coordinates d)
    (h : Torus d → ℝ) :
    h=(tangentMap hd x (rawCoordinates h) : Torus d → ℝ)+graphComplement hd x h := by
  unfold graphComplement
  abel

theorem fourierCoeff_zero_of_meanZero {d : ℕ} (h : Torus d → ℝ) (hm : MeanZero h) :
    fourierCoeff h 0=0 := by
  simp only [fourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,one_mul]
  rw [integral_complex_ofReal,show (∫ x, h x ∂torusMeasure d)=0 from hm]
  rfl

theorem reconstruction_meanZero {d : ℕ} (z : Coordinates d) (w : complement d) :
    MeanZero (reconstruction d (z,w)) := by
  change mean d (reconstruction d (z,w))=0
  rw [reconstruction_apply,map_add,mean_assembly]
  have hw : mean d (w : Space d)=0 := w.property.1
  rw [hw,zero_add]

theorem reconstruction_rawCoordinates {d : ℕ} (z : Coordinates d) (w : complement d) :
    rawCoordinates (reconstruction d (z,w))=z := by
  have hw : coordinates d (w : Space d)=0 := by
    funext i
    change coefficient (axisFrequency i) (w : Space d)=0
    exact (mem_complement_fourier_iff _).mp w.property _ (fun hk => hk.2 ⟨i,Or.inl rfl⟩)
  have he : rawCoordinates (reconstruction d (z,w))=coordinates d (reconstruction d (z,w)) := by
    funext i
    exact (coefficient_eq_fourierCoeff _ _).symm
  rw [he,reconstruction_apply,map_add,coordinates_assembly,hw,add_zero]

theorem raw_sub_complement_supported {d : ℕ} (h : Torus d → ℝ) (v : Space d)
    (hh : MemLp h 2 (torusMeasure d)) (hm : MeanZero h) (hv : MeanZero v)
    (hc : rawCoordinates v=rawCoordinates h) :
    ComplementSupported (fourierCoeff (h-(v : Torus d → ℝ))) := by
  have hvm : MemLp (v : Torus d → ℝ) 2 (torusMeasure d) :=
    v.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  intro k hk
  rw [fourierCoeff_sub h v hh hvm]
  apply sub_eq_zero.mpr
  by_cases hzero : k=0
  · subst k
    rw [fourierCoeff_zero_of_meanZero h hm,fourierCoeff_zero_of_meanZero v hv]
  · have hs : InFirstShell k := Classical.byContradiction (fun hs => hk ⟨hzero,hs⟩)
    obtain ⟨i,hi|hi⟩ := hs
    · subst k
      exact (congrFun hc i).symm
    · subst k
      rw [fourierCoeff_conjugate h,fourierCoeff_conjugate v]
      exact congrArg (starRingEnd ℂ) (congrFun hc i).symm

/-- Nearby graph tangents extract exactly the shell coordinates of every raw
variation and leave a genuine critical-Sobolev complementary residual. -/
theorem graphComplement_properties {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      InCriticalSobolev (tangentMap hd x (rawCoordinates h)) ∧
      MeanZero (tangentMap hd x (rawCoordinates h)) ∧
      InCriticalSobolev (graphComplement hd x h) ∧
      ComplementSupported (fourierCoeff (graphComplement hd x h)) := by
  filter_upwards [tangentMap_equation hd] with x hx h hh hm
  obtain ⟨w,hv,_,hreg⟩ := hx (rawCoordinates h)
  have hmean : MeanZero (tangentMap hd x (rawCoordinates h)) := by
    rw [hv]; exact reconstruction_meanZero _ w
  have hc : rawCoordinates (tangentMap hd x (rawCoordinates h))=rawCoordinates h := by
    rw [hv]; exact reconstruction_rawCoordinates _ w
  exact ⟨hreg,hmean,critical_sub h _ hh hreg,raw_sub_complement_supported h _ hh.1 hm hmean hc⟩

/-- The full actual raw Hessian splits exactly into the graph tangent Hessian
and the strictly complementary Hessian; there is no mixed remainder. -/
theorem secondVariation_decomposition {d : ℕ} (hd : 11 ≤ d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      secondVariation (x.1*spectralThreshold d) (potential hd x) h =
        secondVariation (x.1*spectralThreshold d) (potential hd x)
          (tangentMap hd x (rawCoordinates h))+
        secondVariation (x.1*spectralThreshold d) (potential hd x) (graphComplement hd x h) := by
  filter_upwards [graphComplement_properties hd,hessianPairing_tangentMap_raw_complement hd]
    with x hx hmixed h hh hm
  obtain ⟨hv,_,hq,hc⟩ := hx h hh hm
  have hp := secondVariation_add (by omega : 0<d) (x.1*spectralThreshold d) (potential hd x)
    (tangentMap hd x (rawCoordinates h)) (graphComplement hd x h) hv hq
  rw [← graph_decomposition hd x h,hmixed (rawCoordinates h) _ hq.1 hc,mul_zero,add_zero] at hp
  exact hp

/-- The trusted second variation depends only on the actual a.e. class of a variation. -/
theorem secondVariation_congr_ae {d : ℕ} (β : ℝ) (u : Torus d → ℝ)
    {h q : Torus d → ℝ} (he : h =ᵐ[torusMeasure d] q) :
    secondVariation β u h=secondVariation β u q := by
  have hc (k : Frequency d) : fourierCoeff h k=fourierCoeff q k := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have hE : normalizedPotentialEnergy h=normalizedPotentialEnergy q := by
    unfold normalizedPotentialEnergy potentialEnergy
    congr 1
    apply tsum_congr
    intro k
    simp only [potentialTerm,hc]
  have hs : (∫ x, normalizedGibbs u x*(h x)^2 ∂torusMeasure d)=
      ∫ x, normalizedGibbs u x*(q x)^2 ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have hm : (∫ x, normalizedGibbs u x*h x ∂torusMeasure d)=
      ∫ x, normalizedGibbs u x*q x ∂torusMeasure d := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  simp only [secondVariation,hs,hm,hE]

#print axioms secondVariation_congr_ae
#print axioms normalizedEnergyPairing_summable
#print axioms secondVariation_add
#print axioms graphComplement_properties
#print axioms secondVariation_decomposition
end BecknerOnofri.HighDim.LocalEleven.FullHessianDecomposition
