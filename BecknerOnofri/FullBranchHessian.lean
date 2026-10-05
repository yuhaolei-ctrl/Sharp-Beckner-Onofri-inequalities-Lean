module

public import BecknerOnofri.FullReducedHessian
public import BecknerOnofri.FullHessianDecomposition
public import BecknerOnofri.AngularTangentRepresentation

@[expose] public section

/-! The complete actual raw critical-Sobolev Hessian on the diagonal branch:
nonpositivity, a quantitative split gap, and the exact translation kernel. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.FullBranchHessian
open ContinuousGibbs ContinuousFirstShell ReducedEquation ReducedCubicExpansion
open DiagonalScalarBranch FullReducedHessian ReducedHessianCoercivity
open GraphHessian FullHessianDecomposition AngularTangentRepresentation
open ComplementHessian RawComplementGap GraphTranslationTangents

def diagonalInput {d : ℕ} (hd : 12≤d) (μ : ℝ) : ℝ × Coordinates d :=
  (μ,realDiagonal d (amplitude hd μ))

theorem diagonalInput_tendsto {d : ℕ} (hd : 12≤d) :
    Tendsto (diagonalInput hd) (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
  have hz := ((realDiagonal d).continuous.continuousAt.tendsto (x := 0)).comp (amplitude_tendsto hd)
  simp only [map_zero] at hz
  exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz

theorem diagonalPotential_tendsto {d : ℕ} (hd : 12≤d) :
    Tendsto (fun μ => potential hd (diagonalInput hd μ)) (𝓝[>] (1:ℝ)) (𝓝 0) :=
  (UniformComplementBounds.potential_tendsto hd).comp (diagonalInput_tendsto hd)

/-- Zero Fourier energy on the actual complement means zero almost everywhere. -/
theorem complement_energy_zero {d : ℕ} (hd : 12≤d) (q : Torus d → ℝ)
    (hq : InCriticalSobolev q) (hc : ComplementSupported (fourierCoeff q))
    (he : normalizedPotentialEnergy q=0) : q =ᵐ[torusMeasure d] (fun _ => 0) := by
  have hg := normalizedEnergy_gap hd q hq hc
  rw [he] at hg
  have hn : 0≤∫ x, (q x)^2 ∂torusMeasure d := integral_nonneg (fun _ => sq_nonneg _)
  have hz : (∫ x, (q x)^2 ∂torusMeasure d)=0 := by linarith
  have hi : Integrable (fun x => (q x)^2) (torusMeasure d) := by
    convert! hq.1.integrable_mul hq.1 using 1
    funext x
    change q x^2=q x*q x
    ring
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (q x)) hi).mp hz
  filter_upwards [hae] with x hx
  exact sq_eq_zero_iff.mp hx

/-- The actual raw Hessian has a quantitative gap on both the real shell
and the entire complementary critical-Sobolev subspace. -/
theorem diagonal_secondVariation_bound {d : ℕ} (hd : 12≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤
        -2*onset μ*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-
          (15/32:ℝ)*normalizedPotentialEnergy (graphComplement hd (diagonalInput hd μ) h) := by
  filter_upwards [(diagonalInput_tendsto hd).eventually (secondVariation_decomposition hd),
    (diagonalInput_tendsto hd).eventually (graphComplement_properties hd),
    diagonal_graph_hessian_bound hd,(diagonalPotential_tendsto hd).eventually
      (normalized_le_two_near_zero d),self_mem_nhdsWithin,
    (gt_mem_nhds (by norm_num : (1:ℝ)<2)).filter_mono nhdsWithin_le_nhds]
    with μ hsplit hprops hfinite hpot hμ hμ2 h hh hm
  change 1<μ at hμ
  obtain ⟨hv,hvm,hq,hc⟩ := hprops h hh hm
  have hcomp := secondVariation_complement_bound hd (show 0<μ by linarith) hμ2.le
    _ hpot _ hq hc
  have hfin := hfinite (rawCoordinates h)
  simp only [diagonalInput] at hsplit hcomp ⊢
  rw [hsplit h hh hm]
  linarith

/-- Full raw-domain nonpositivity and exactly the translation tangent kernel. -/
theorem diagonal_hessian_nonpos_kernel {d : ℕ} (hd : 12≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ), ∀ h : Torus d → ℝ, InCriticalSobolev h → MeanZero h →
      secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤ 0 ∧
      (secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h=0 ↔
        ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination (potential hd (diagonalInput hd μ)) a) := by
  filter_upwards [diagonal_secondVariation_bound hd,
    (diagonalInput_tendsto hd).eventually (graphComplement_properties hd),
    (diagonalInput_tendsto hd).eventually (imaginary_tangent_representation hd),
    (diagonalInput_tendsto hd).eventually (tangentMap_angles hd),
    diagonal_graph_hessian_nonpos_kernel hd,eventually_parameter_interval hd,self_mem_nhdsWithin]
    with μ hbound hprops hrepr hang hfinite hinterval hμ h hh hm
  change 1<μ at hμ
  let q := graphComplement hd (diagonalInput hd μ) h
  obtain ⟨hv,hvm,hq,hc⟩ := hprops h hh hm
  have hE : 0≤normalizedPotentialEnergy q := normalizedEnergy_nonneg (by omega) q hq
  have hS : 0≤amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h)) := amplitudeSquare_nonneg _
  have hδ := onset_pos hμ
  have hb := hbound h hh hm
  change secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) h ≤
    -2*onset μ*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-(15/32:ℝ)*normalizedPotentialEnergy q at hb
  refine ⟨le_trans hb (by nlinarith [mul_nonneg hδ.le hS]),?_⟩
  constructor
  · intro hz
    rw [hz] at hb
    have hEq : normalizedPotentialEnergy q=0 := by nlinarith [mul_nonneg hδ.le hS]
    have hSq : amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))=0 := by nlinarith
    have hr : FullReducedHessian.realPart (rawCoordinates h)=0 := by
      by_contra hr
      have := amplitudeSquare_pos hr
      linarith
    have hqa := complement_energy_zero hd q hq hc hEq
    have hre : ∀ i, (rawCoordinates h i).re=0 := fun i => congrFun hr i
    obtain ⟨a,ha⟩ := hrepr (amplitude hd μ) (amplitude_pos hd hμ hinterval.2).ne' rfl
      (rawCoordinates h) hre
    refine ⟨a,?_⟩
    filter_upwards [hqa] with y hy
    have he := congrFun (graph_decomposition hd (diagonalInput hd μ) h) y
    change h y=tangentMap hd (diagonalInput hd μ) (rawCoordinates h) y+q y at he
    rw [hy,add_zero] at he
    exact he.trans (congrFun ha y)
  · rintro ⟨a,ha⟩
    let z : Coordinates d := ∑ j : Fin d, a j • angularDirection (diagonalInput hd μ).2 j
    have hr : FullReducedHessian.realPart z=0 := by
      funext i
      exact real_part_angle_sum_zero (amplitude hd μ) a i
    have hz : secondVariation (μ*spectralThreshold d) (potential hd (diagonalInput hd μ))
        (tangentMap hd (diagonalInput hd μ) z)=0 := (hfinite z).2.mpr hr
    have htan := hang a
    have hae : h =ᵐ[torusMeasure d] (tangentMap hd (diagonalInput hd μ) z : Torus d → ℝ) := by
      rw [show (tangentMap hd (diagonalInput hd μ) z : Torus d → ℝ)=
        tangentCombination (potential hd (diagonalInput hd μ)) a from htan]
      exact ha
    exact (secondVariation_congr_ae (μ*spectralThreshold d) (potential hd (diagonalInput hd μ)) hae).trans hz

/-- The same full Hessian theorem in the exact trusted physical branch notation. -/
theorem physical_hessian_nonpos_kernel {d : ℕ} (hd : 12≤d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      secondVariation β (physicalPotential hd β) h ≤ 0 ∧
      (secondVariation β (physicalPotential hd β) h=0 ↔
        ∃ a : Fin d → ℝ, h =ᵐ[torusMeasure d] tangentCombination (physicalPotential hd β) a) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_hessian_nonpos_kernel hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h hh hm
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (diagonalInput hd (β/spectralThreshold d)) := by
    simp only [physicalPotential,branchPotential,hi,diagonalInput]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ] using hb h hh hm

theorem physical_secondVariation_bound {d : ℕ} (hd : 12≤d) :
    ∀ᶠ β in 𝓝[>] (spectralThreshold d), ∀ h : Torus d → ℝ,
      InCriticalSobolev h → MeanZero h →
      secondVariation β (physicalPotential hd β) h ≤
        -2*onsetDelta d β*amplitudeSquare (FullReducedHessian.realPart (rawCoordinates h))-
          (15/32:ℝ)*normalizedPotentialEnergy
            (graphComplement hd (diagonalInput hd (β/spectralThreshold d)) h) := by
  filter_upwards [(normalized_parameter_tendsto hd).eventually (diagonal_secondVariation_bound hd),
    (normalized_parameter_tendsto hd).eventually (amplitude_eventually_inverse hd)] with β hb hi h hh hm
  have hσ : spectralThreshold d≠0 := (Legacy.TorusEndpoint.endpointSigma_pos (by omega : 0<d)).ne'
  have he : physicalPotential hd β=potential hd (diagonalInput hd (β/spectralThreshold d)) := by
    simp only [physicalPotential,branchPotential,hi,diagonalInput]
  rw [he]
  simpa only [div_mul_cancel₀ _ hσ,physical_onset_eq hd] using hb h hh hm

#print axioms physical_secondVariation_bound
#print axioms diagonal_secondVariation_bound
#print axioms diagonal_hessian_nonpos_kernel
#print axioms physical_hessian_nonpos_kernel
end BecknerOnofri.HighDim.FullBranchHessian
