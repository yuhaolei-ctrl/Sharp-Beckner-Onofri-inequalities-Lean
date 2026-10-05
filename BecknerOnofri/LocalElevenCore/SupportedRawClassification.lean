import BecknerOnofri.GeneralSobolevEmbedding
import BecknerOnofri.RawSubspectralLocalUniqueness
import BecknerOnofri.LocalElevenCore.SupportedDeltaExhaustiveness

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SupportedFamily
open ContinuousGibbs

/-- Exhaustiveness on the original raw H^s domain for every s>d/2. -/
theorem raw_sobolev_classification {d : ℕ} (hd : 11≤d) (s : ℝ) (hs : (d:ℝ)/2<s) :
    ∃ ε : ℝ,0<ε ∧ ∀ (μ : ℝ) (u : Torus d → ℝ),
      InSobolev s u → MeanZero u → |μ-1|<ε → sobolevNorm s u<ε →
      (∀ k : NonzeroFrequency d,((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
        (μ:ℂ)*fourierCoeff (normalizedGibbs u) k.val) →
      ¬u =ᵐ[torusMeasure d] (fun _ => 0) →
      0<1-1/μ ∧ ∃ I : Finset (Fin d),I.Nonempty ∧ ∃ a : Torus d,
        u =ᵐ[torusMeasure d] (ContinuousSymmetry.translation a (branch hd I (1-1/μ)) : Torus d → ℝ) := by
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp (small_solution_branch hd)
  let C := ‖SobolevEmbedding.inverseScaleLp (by omega : 0<d) hs‖
  have hC : 0≤C := norm_nonneg _
  refine ⟨min δ (δ/(C+1)),lt_min hδ (div_pos hδ (by positivity)),?_⟩
  intro μ u hu hm hμ hn hEuler hnzero
  obtain ⟨v,hvu,hv,hbound⟩ := SobolevEmbedding.exists_continuous_representative (by omega) hs u hu
  have hvn : ‖v‖<δ := by
    have hsmall : sobolevNorm s u<δ/(C+1) := hn.trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp hsmall
    have hN : 0≤sobolevNorm s u := Real.sqrt_nonneg _
    change ‖v‖≤C*sobolevNorm s u at hbound
    nlinarith
  have hmv : MeanZero v := (integral_congr_ae hvu).trans hm
  have heq : ReducedEquation.full d μ v=0 := by
    apply (ReducedEquation.full_zero_iff_stationary (by omega) _ v).mpr
    refine ⟨hmv,fun k => ?_⟩
    rw [fourierCoeff_congr_ae hvu,
      fourierCoeff_congr_ae (RawSubspectralLocalUniqueness.gibbs_congr_ae hvu)]
    exact hEuler k
  have hvzero : v≠0 := by
    intro he
    apply hnzero
    filter_upwards [hvu] with x hx
    simpa only [he,ContinuousMap.zero_apply] using hx.symm
  have hdist : dist (μ,v) (1,(0:Space d))<δ := by
    simpa only [Prod.dist_eq,Real.dist_eq,dist_zero_right,max_lt_iff] using
      And.intro (hμ.trans_le (min_le_left _ _)) hvn
  obtain ⟨hp,I,hI,a,ha⟩ := hlocal hdist hmv heq hvzero
  exact ⟨hp,I,hI,a,hvu.symm.trans (Filter.Eventually.of_forall (fun x => congrArg (fun f : Space d => f x) ha))⟩

#print axioms raw_sobolev_classification
end BecknerOnofri.HighDim.LocalEleven.SupportedFamily
