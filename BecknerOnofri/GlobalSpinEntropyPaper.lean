import BecknerOnofri.GlobalShapeEntropyPaper

/-! A single witness for both clauses of the manuscript's general spin entropy
proposition, with the original uncompressed probability laws. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace BecknerOnofri.HighDim.ShapeEntropy

lemma exchangeable_mean_eq {ν : Spin.Configuration → ℝ} (hν : Spin.Exchangeable ν)
    {t : ℝ} (ht : ∑ σ : Spin.Configuration,ν σ*Spin.jointSpin {(0 : Fin 12)} σ=t) :
    Spin.mean (Spin.countLaw ν)=t := by
  have h := Spin.exchangeable_joint_moment hν 0
  simp_rw [Spin.firstCoordinates_zero,Spin.moment_zero_eq_meanCoordinate] at h
  exact h.symm.trans ht

lemma channel_single_mean {ρ : ProbabilityDensity 12} (D : Data ρ) (i : Fin 12) :
    (∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Spin.jointSpin {i} σ)=
      (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re := by
  rw [Spin.channelLaw_joint_moment]
  simp only [Finset.prod_singleton,Spin.torusCosines]
  rw [density_axis_mean D,density_axis_re D,density_axis_mean D]

/-- The existential witness is outside both universal quantifiers: the same
function works for every shape density and every admissible spin law. -/
theorem global_spin_entropy :
    ∃ ψ : ℝ → ℝ,
      ContinuousOn ψ (Icc (0 : ℝ) 1) ∧ ConvexOn ℝ (Icc (0 : ℝ) 1) ψ ∧
      MonotoneOn ψ (Icc (0 : ℝ) 1) ∧ (∀ t∈Icc (0 : ℝ) 1,0≤ψ t) ∧
      (∀ t∈Icc (0 : ℝ) (1/16),ψ t=(3/40 : ℝ)*t^4) ∧
      (∀ (ρ : ProbabilityDensity 12), SmoothOnTorus ρ.value →
        (∀ x,0<ρ.value x) →
        (∀ (π : Equiv.Perm (Fin 12)) (x : Torus 12),ρ.value (fun i => x (π i))=ρ.value x) →
        IsCountableCosineMixture ρ →
        ∀ (V : (Fin 12 → ℝ) → ℝ), ContDiffOn ℝ ∞ V (ConditionalEntropy.cosineCube 12) →
        (∀ x,Real.log (ρ.value x)=V (ConditionalEntropy.cosineVector x)) →
        (∀ v∈ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤cosinePartial i V v) →
        (∀ v∈ConditionalEntropy.cosineCube 12,∀ i : Fin 12,0≤cosinePartial i (cosinePartial i V) v) →
        (∀ σ,0≤Spin.channelLaw ρ σ) ∧ (∑ σ : Spin.Configuration,Spin.channelLaw ρ σ)=1 ∧
        Spin.Exchangeable (Spin.channelLaw ρ) ∧
        (∀ i : Fin 12,(∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Spin.jointSpin {i} σ)=
          (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re) ∧
        Spin.channelLaw ρ ∅≤1/4096 ∧
        2*(∑ σ : Spin.Configuration,Spin.channelLaw ρ σ*Real.log (Spin.channelLaw ρ σ/(1/4096)))+
          12*ψ (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re+
          (∑ i : Fin 12,((21/1000)*‖fourierCoeff ρ.value (Pi.single i (2 : ℤ))‖^2+
            (27/40)*∑' n : ℕ,‖fourierCoeff ρ.value (Pi.single i (n+3 : ℤ))‖^2/(n+3 : ℝ)))≤entropy ρ) ∧
      (∀ (ν : Spin.Configuration → ℝ), (∀ σ,0≤ν σ) →
        (∑ σ : Spin.Configuration,ν σ)=1 → Spin.Exchangeable ν →
        ν ∅≤1/4096 → ∀ t∈Icc (0 : ℝ) 1,
        (∀ i : Fin 12,(∑ σ : Spin.Configuration,ν σ*Spin.jointSpin {i} σ)=t) →
        t^4/250≤2*(∑ σ : Spin.Configuration,ν σ*Real.log (ν σ/(1/4096)))-
          (∑ s : Spin.Order,Spin.weight s*(∑ σ : Spin.Configuration,ν σ*Spin.jointSpin (Spin.firstCoordinates s) σ)^2)+
          12*ψ t) := by
  obtain ⟨ψ,hc,hcv,hm,hn,hsmall,hminor,hspin⟩ := exists_certified_entropy_minorant
  refine ⟨ψ,hc,hcv,hm,hn,hsmall,?_,?_⟩
  · intro ρ hs hp hperm hmix V hV hlog h1 h2
    let D := paperData ρ hs hp hperm hmix V hV hlog h1 h2
    refine ⟨Spin.channelLaw_nonneg ρ,Spin.channelLaw_mass ρ,exchangeable D,
      channel_single_mean D,?_,?_⟩
    · simpa [Spin.countLaw,Spin.countClass] using (feasible D).2.2
    · have hb := (channel_fourier_entropy D ψ hc hcv hminor).2
      rw [Spin.exchangeable_entropy (exchangeable D)]
      have he : Spin.mean (Spin.countLaw (Spin.channelLaw ρ))=
          (fourierCoeff ρ.value (Pi.single (0 : Fin 12) (1 : ℤ))).re := by
        rw [density_axis_re D,density_axis_mean D]
      rw [he] at hb
      simpa only [Finset.sum_add_distrib,← Finset.mul_sum,add_assoc] using hb
  · intro ν hnν hmass hex hcap t ht hmean
    have hf : Spin.Feasible (Spin.countLaw ν) := by
      refine ⟨Spin.countLaw_nonneg hnν,?_,?_⟩
      · rw [Spin.countLaw_mass,hmass]
      · simpa [Spin.countLaw,Spin.countClass] using hcap
    have he := exchangeable_mean_eq hex (hmean 0)
    have hb := hspin (Spin.countLaw ν) hf (he ▸ ht)
    rw [he] at hb
    rw [Spin.exchangeable_entropy hex,Spin.exchangeable_energy hex]
    exact hb

#print axioms global_spin_entropy
end BecknerOnofri.HighDim.ShapeEntropy
