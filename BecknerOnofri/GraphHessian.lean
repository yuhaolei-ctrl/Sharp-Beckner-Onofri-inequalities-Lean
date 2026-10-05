module

public import BecknerOnofri.GraphHessianFourier

@[expose] public section

/-! Exact physical Hessian on the genuine implicit complementary graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.GraphHessian
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open GreenPairing GraphEnergy ReducedEnergyGradient

/-- The actual bilinear covariance minus the physical Fourier-energy pairing. -/
def hessianPairing {d : ℕ} (β : ℝ) (u v q : Torus d → ℝ) : ℝ :=
  (∫ x, normalizedGibbs u x*v x*q x ∂torusMeasure d) -
    (∫ x, normalizedGibbs u x*v x ∂torusMeasure d)*
      (∫ x, normalizedGibbs u x*q x ∂torusMeasure d) -
        spectralThreshold d/β*normalizedEnergyPairing v q

theorem hessianPairing_self {d : ℕ} (hd : 0<d) (β : ℝ) (u v : Torus d → ℝ)
    (hv : InCriticalSobolev v) : hessianPairing β u v v=secondVariation β u v := by
  rw [hessianPairing,normalizedEnergyPairing_self hd v hv]
  simp only [secondVariation,pow_two,mul_assoc]

theorem hessianPairing_continuous {d : ℕ} (β : ℝ) (u v q : Space d) :
    hessianPairing β u v q = mean d (normalizedDerivative u v*q)-
      spectralThreshold d/β*normalizedEnergyPairing v q := by
  rw [← show logPartitionHessian u v q=mean d (normalizedDerivative u v*q) from rfl,
    logPartitionHessian_apply]
  simp only [hessianPairing,weightedMean_apply,mean_apply,ContinuousMap.mul_apply,
    normalized_apply,mul_assoc]

theorem physical_factor {d : ℕ} (hd : 0<d) (μ : ℝ) :
    spectralThreshold d/(μ*spectralThreshold d)=1/μ := by
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos hd).ne'
  field_simp

/-- The derivative of the actual graph equation, with no imposed stationarity. -/
theorem differentiated_projected_equation {d : ℕ} (hd : 0<d) (μ : ℝ)
    {ψ : Coordinates d → complement d} {ψ' : Coordinates d →L[ℝ] complement d}
    {z : Coordinates d} (hψ : HasFDerivAt ψ ψ' z)
    (he : ∀ᶠ y in 𝓝 z, projectedEquation (greenContinuous d) ((μ,y),ψ y)=0)
    (h : Coordinates d) :
    (ψ' h : Space d)=μ • projectedGreen d
      (normalizedDerivative (reconstruction d (z,ψ z)) (reconstruction d (h,ψ' h))) := by
  let w' : Coordinates d →L[ℝ] Space d := (complement d).subtypeL.comp ψ'
  let u' : Coordinates d →L[ℝ] Space d := assembly d+w'
  let u := reconstruction d (z,ψ z)
  have hw : HasFDerivAt (fun y => (ψ y : Space d)) w' z := by
    convert! (complement d).subtypeL.hasFDerivAt.comp z hψ using 1
  have hu : HasFDerivAt (fun y => reconstruction d (y,ψ y)) u' z := by
    convert! (assembly d).hasFDerivAt.add hw using 1
  have hn : HasFDerivAt (fun y => normalized (reconstruction d (y,ψ y)))
      ((normalizedDerivative u).comp u') z := by
    convert! (hasFDerivAt_normalized u).comp z hu using 1
  have hec : (fun y => (ψ y : Space d)) =ᶠ[𝓝 z]
      (fun y => μ • projectedGreen d (normalized (reconstruction d (y,ψ y)))) := by
    filter_upwards [he] with y hy
    exact projected_equation_value hd μ y (ψ y) hy
  have hg : HasFDerivAt (fun y => μ • projectedGreen d (normalized (reconstruction d (y,ψ y))))
      (μ • ((projectedGreen d).comp ((normalizedDerivative u).comp u'))) z := by
    convert! ((projectedGreen d).hasFDerivAt.comp z hn).const_smul μ using 1
  exact congrArg (fun L : Coordinates d →L[ℝ] Space d => L h)
    (hw.unique (hg.congr_of_eventuallyEq hec))

theorem shell_residual_pairing {d : ℕ} {μ : ℝ} (hμ : μ≠0)
    (h : Coordinates d) (a : Space d) :
    mean d (a*assembly d h)-(1/μ)*mean d ((assembly d h)^2) =
      -(2/μ)*(∑ i, conj (h i)*(h-μ • coordinates d a) i).re := by
  rw [pow_two,mean_mul_assembly,mean_mul_assembly,coordinates_assembly]
  have hs : (∑ i, conj (h i)*(h-μ • coordinates d a) i) =
      (∑ i,conj (h i)*h i)-(μ:ℂ)*(∑ i,conj (h i)*coordinates d a i) := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply,Pi.smul_apply,Complex.real_smul]
    ring
  rw [hs]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  field_simp
  ring

/-- The true quadratic Hessian on a linearized complementary solution. -/
theorem secondVariation_linearized {d : ℕ} (hd : 0<d) {μ : ℝ} (hμ : μ≠0)
    (u : Space d) (h : Coordinates d) (w : complement d)
    (hw : (w : Space d)=μ • projectedGreen d
      (normalizedDerivative u (reconstruction d (h,w)))) :
    secondVariation (μ*spectralThreshold d) u (reconstruction d (h,w)) =
      -(2/μ)*(∑ i,conj (h i)*(h-μ • coordinates d
        (normalizedDerivative u (reconstruction d (h,w)))) i).re := by
  let v := reconstruction d (h,w)
  let a := normalizedDerivative u v
  have hv := linearized_inCriticalSobolev hd μ h w a hw
  rw [← hessianPairing_self hd _ u _ hv,hessianPairing_continuous,physical_factor hd,
    normalizedEnergyPairing_self hd _ hv,linearized_normalizedEnergy hd μ h w a hw]
  change mean d (a*v)-(1/μ)*(2*∑ i,‖h i‖^2+μ*mean d ((w : Space d)*a)) = _
  have he : mean d (a*v)=mean d (a*assembly d h)+mean d ((w : Space d)*a) := by
    rw [show v=assembly d h+(w : Space d) from rfl,mul_add,map_add,mul_comm a (w : Space d)]
  rw [he,← assembly_square_mean]
  calc
    _ = mean d (a*assembly d h)-(1/μ)*mean d ((assembly d h)^2) := by field_simp; ring
    _ = _ := shell_residual_pairing hμ h a

/-- Exact mixed orthogonality against every continuous complementary direction. -/
theorem hessianPairing_linearized_complement {d : ℕ} (hd : 0<d) {μ : ℝ} (hμ : μ≠0)
    (u : Space d) (h : Coordinates d) (w q : complement d)
    (hw : (w : Space d)=μ • projectedGreen d
      (normalizedDerivative u (reconstruction d (h,w)))) :
    hessianPairing (μ*spectralThreshold d) u (reconstruction d (h,w)) (q : Space d)=0 := by
  rw [hessianPairing_continuous,physical_factor hd,linearized_pairing_complement hd μ h w q _ hw]
  field_simp
  ring

/-- Derivative of the full-coordinate reduced equation for a differentiable graph. -/
theorem hasFDerivAt_graphResidual {d : ℕ} (μ : ℝ)
    {ψ : Coordinates d → complement d} {ψ' : Coordinates d →L[ℝ] complement d}
    {z : Coordinates d} (hψ : HasFDerivAt ψ ψ' z) :
    HasFDerivAt (fun y => y-μ • coordinates d (normalized (reconstruction d (y,ψ y))))
      (ContinuousLinearMap.id ℝ (Coordinates d)-μ • ((coordinates d).comp
        ((normalizedDerivative (reconstruction d (z,ψ z))).comp
          (assembly d+(complement d).subtypeL.comp ψ')))) z := by
  have hw := (complement d).subtypeL.hasFDerivAt.comp z hψ
  have hu : HasFDerivAt (fun y => reconstruction d (y,ψ y))
      (assembly d+(complement d).subtypeL.comp ψ') z := by
    convert! (assembly d).hasFDerivAt.add hw using 1
  have hn := (hasFDerivAt_normalized (reconstruction d (z,ψ z))).comp z hu
  convert! (hasFDerivAt_id z).sub (((coordinates d).hasFDerivAt.comp z hn).const_smul μ) using 1

theorem secondVariation_graph {d : ℕ} (hd : 0<d) {μ : ℝ} (hμ : μ≠0)
    {ψ : Coordinates d → complement d} {ψ' : Coordinates d →L[ℝ] complement d}
    {z : Coordinates d} (hψ : HasFDerivAt ψ ψ' z)
    (he : ∀ᶠ y in 𝓝 z, projectedEquation (greenContinuous d) ((μ,y),ψ y)=0)
    (h : Coordinates d) :
    secondVariation (μ*spectralThreshold d) (reconstruction d (z,ψ z)) (reconstruction d (h,ψ' h)) =
      -(2/μ)*(∑ i,conj (h i)*(fderiv ℝ
        (fun y => y-μ • coordinates d (normalized (reconstruction d (y,ψ y)))) z h) i).re := by
  rw [(hasFDerivAt_graphResidual μ hψ).fderiv]
  exact secondVariation_linearized hd hμ _ h (ψ' h)
    (differentiated_projected_equation hd μ hψ he h)

/-- A graph tangent is the actual derivative in the first-shell variables. -/
def tangentMap {d : ℕ} (hd : 12≤d) (x : ℝ × Coordinates d) : Coordinates d →L[ℝ] Space d :=
  (fderiv ℝ (potential hd) x).comp
    ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d)))

@[simp] theorem tangentMap_apply {d : ℕ} (hd : 12≤d) (x : ℝ × Coordinates d) (h : Coordinates d) :
    tangentMap hd x h=fderiv ℝ (potential hd) x (0,h) := rfl

theorem tangentMap_eq {d : ℕ} (hd : 12≤d) {x : ℝ × Coordinates d}
    (hp : DifferentiableAt ℝ (potential hd) x)
    {ψ' : Coordinates d →L[ℝ] complement d}
    (hψ : HasFDerivAt (fun z => correction hd (x.1,z)) ψ' x.2) :
    tangentMap hd x=assembly d+(complement d).subtypeL.comp ψ' := by
  have ht : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d))) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hw := (complement d).subtypeL.hasFDerivAt.comp x.2 hψ
  have hrec : HasFDerivAt (fun z => potential hd (x.1,z))
      (assembly d+(complement d).subtypeL.comp ψ') x.2 := by
    convert! (assembly d).hasFDerivAt.add hw using 1
  have hf : HasFDerivAt (fun z => potential hd (x.1,z)) (tangentMap hd x) x.2 := by
    convert! hp.hasFDerivAt.comp x.2 ht using 1
  exact hf.unique hrec

/-- Genuine critical-Sobolev graph tangents, with the exact differentiated Euler equation. -/
theorem tangentMap_equation {d : ℕ} (hd : 12≤d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ h : Coordinates d,
      ∃ w : complement d, tangentMap hd x h=reconstruction d (h,w) ∧
        (w : Space d)=x.1 • projectedGreen d (normalizedDerivative (potential hd x) (tangentMap hd x h)) ∧
        InCriticalSobolev (tangentMap hd x h) := by
  filter_upwards [(correction_solves hd).eventually_nhds,
    (correction_analytic hd).eventually_analyticAt,(potential_analytic hd).eventually_analyticAt]
    with x he hc hp h
  have ht : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d))) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hψ : DifferentiableAt ℝ (fun z => correction hd (x.1,z)) x.2 := by
    convert! hc.differentiableAt.comp x.2 ht.differentiableAt using 1
  let ψ' := fderiv ℝ (fun z => correction hd (x.1,z)) x.2
  have hv : tangentMap hd x h=reconstruction d (h,ψ' h) := by
    rw [tangentMap_eq hd hp.differentiableAt hψ.hasFDerivAt]
    rfl
  have hes : ∀ᶠ z in 𝓝 x.2,
      projectedEquation (greenContinuous d) ((x.1,z),correction hd (x.1,z))=0 :=
    ht.continuousAt.tendsto.eventually he
  have hw := differentiated_projected_equation (by omega : 0<d) x.1 hψ.hasFDerivAt hes h
  change (ψ' h : Space d)=x.1 • projectedGreen d
    (normalizedDerivative (potential hd x) (reconstruction d (h,ψ' h))) at hw
  refine ⟨ψ' h,hv,?_,?_⟩
  · simpa only [hv] using hw
  · rw [hv]
    exact linearized_inCriticalSobolev (by omega) x.1 h (ψ' h) _ hw

/-- Exact physical second variation on the actual graph tangent, expressed
through the actual reduced Jacobian; valid even before imposing reduced=0. -/
theorem secondVariation_tangentMap {d : ℕ} (hd : 12≤d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ h : Coordinates d,
      secondVariation (x.1*spectralThreshold d) (potential hd x) (tangentMap hd x h) =
        -(2/x.1)*(∑ i,conj (h i)*(fderiv ℝ (fun z => reduced hd (x.1,z)) x.2 h) i).re := by
  have hpos : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0<x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [(correction_solves hd).eventually_nhds,
    (correction_analytic hd).eventually_analyticAt,(potential_analytic hd).eventually_analyticAt,hpos]
    with x he hc hp hμ h
  have ht : HasFDerivAt (fun z : Coordinates d => (x.1,z))
      ((0 : Coordinates d →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Coordinates d))) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hψ : DifferentiableAt ℝ (fun z => correction hd (x.1,z)) x.2 := by
    convert! hc.differentiableAt.comp x.2 ht.differentiableAt using 1
  have hes : ∀ᶠ z in 𝓝 x.2,
      projectedEquation (greenContinuous d) ((x.1,z),correction hd (x.1,z))=0 :=
    ht.continuousAt.tendsto.eventually he
  rw [tangentMap_eq hd hp.differentiableAt hψ.hasFDerivAt]
  exact secondVariation_graph (by omega) hμ.ne' hψ.hasFDerivAt hes h

theorem hessianPairing_tangentMap_complement {d : ℕ} (hd : 12≤d) :
    ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)), ∀ (h : Coordinates d) (q : complement d),
      hessianPairing (x.1*spectralThreshold d) (potential hd x) (tangentMap hd x h) (q : Space d)=0 := by
  have hpos : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0), 0<x.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [tangentMap_equation hd,hpos] with x hx hμ h q
  obtain ⟨w,hv,hw,hreg⟩ := hx h
  rw [hv] at hw ⊢
  exact hessianPairing_linearized_complement (by omega) hμ.ne' _ h w q hw

#print axioms tangentMap_equation
#print axioms secondVariation_tangentMap
#print axioms hessianPairing_tangentMap_complement
#print axioms differentiated_projected_equation
#print axioms secondVariation_linearized
#print axioms hessianPairing_linearized_complement
end BecknerOnofri.HighDim.GraphHessian
