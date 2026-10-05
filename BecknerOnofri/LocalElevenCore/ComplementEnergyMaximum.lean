module

public import BecknerOnofri.LocalElevenCore.ContinuousEnergyAlongLine

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy
open ContinuousGibbs ContinuousFirstShell ContinuousComplement ReducedEquation GreenLocalBranch
open GraphHessian ReducedEnergyGradient ComplementHessian RawComplementGap

theorem value_add_le_of_hessian_nonpos {d : ℕ} (hd : 0<d) (μ : ℝ) (u q : Space d)
    (hu : InCriticalSobolev u) (hq : InCriticalSobolev q)
    (hfirst : lineDerivative μ u q 0=0)
    (hsecond : ∀ t : ℝ,t∈Icc (0:ℝ) 1 → secondVariation (μ*spectralThreshold d) (u+t • q) q≤0) :
    value μ (u+q)≤value μ u := by
  have hD : AntitoneOn (lineDerivative μ u q) (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t ht => (lineDerivative_hasDerivAt hd μ u q t).continuousAt.continuousWithinAt)
      (fun t ht => (lineDerivative_hasDerivAt hd μ u q t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(lineDerivative_hasDerivAt hd μ u q t).deriv]
    exact hsecond t (interior_subset ht)
  have hF : AntitoneOn (fun t : ℝ => value μ (u+t • q)) (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun t ht => (value_line_hasDerivAt hd μ u q hu hq t).continuousAt.continuousWithinAt)
      (fun t ht => (value_line_hasDerivAt hd μ u q hu hq t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(value_line_hasDerivAt hd μ u q hu hq t).deriv]
    have ht' : t∈Icc (0:ℝ) 1 := interior_subset ht
    have h := hD (by simp : (0:ℝ)∈Icc (0:ℝ) 1) ht' ht'.1
    simpa only [hfirst] using h
  simpa only [one_smul,zero_smul,add_zero] using
    hF (by simp : (0:ℝ)∈Icc (0:ℝ) 1) (by simp : (1:ℝ)∈Icc (0:ℝ) 1) (by norm_num)

/-- The complementary implicit graph truly maximizes the physical energy in the
complement direction, uniformly near the bifurcation point. -/
theorem exists_complement_energy_bound {d : ℕ} (hd : 11≤d) :
    ∃ ε : ℝ,0<ε ∧ ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),
      ∀ q : complement d,InCriticalSobolev (q : Space d) → ‖(q : Space d)‖<ε →
      dualFunctional (x.1*spectralThreshold d) (potential hd x+(q : Space d))≤
        dualFunctional (x.1*spectralThreshold d) (potential hd x) := by
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp (normalized_le_two_near_zero d)
  have ht : Tendsto (potential hd) (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
    have hb : potential hd (1,0)=0 := by simp [potential,correction_base]
    simpa only [hb] using (potential_analytic hd).continuousAt.tendsto
  have hsmall : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),‖potential hd x‖<ρ/2 :=
    ht.norm.eventually (gt_mem_nhds (by simpa using half_pos hρ))
  have hμ : ∀ᶠ x : ℝ × Coordinates d in 𝓝 (1,0),0<x.1 ∧ x.1<2 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  refine ⟨ρ/2,half_pos hρ,?_⟩
  filter_upwards [correction_solves hd,GraphCritical.potential_inCriticalSobolev hd,hsmall,hμ]
    with x he hu hsmall hμ
  intro q hq hqsmall
  have hw := projected_equation_value (by omega : 0<d) x.1 x.2 (correction hd x) he
  have hp := linearized_pairing_complement (by omega : 0<d) x.1 x.2 (correction hd x) q
    (normalized (potential hd x)) hw
  have hfirst : lineDerivative x.1 (potential hd x) (q : Space d) 0=0 := by
    change normalizedEnergyPairing (potential hd x) (q : Space d)=
      x.1*weightedMean (potential hd x) (q : Space d) at hp
    simp only [lineDerivative,zero_smul,add_zero,zero_mul,hp]
    field_simp [hμ.1.ne']
    ring
  have hsecond (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      secondVariation (x.1*spectralThreshold d) (potential hd x+t • (q : Space d)) (q : Space d)≤0 := by
    have hnorm : ‖potential hd x+t • (q : Space d)‖<ρ := by
      have h := norm_add_le (potential hd x) (t • (q : Space d))
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at h
      have hmul := mul_le_of_le_one_left (norm_nonneg (q : Space d)) ht.2
      linarith
    have hG := hball (by simpa only [dist_zero_right] using hnorm)
    have hc : ComplementSupported (fourierCoeff (q : Space d)) := by
      intro k hk
      rw [← coefficient_eq_fourierCoeff]
      exact (mem_complement_fourier_iff _).mp q.property k hk
    have hb := secondVariation_complement_bound hd hμ.1 hμ.2.le _ hG _ hq hc
    have hEn := normalizedEnergy_nonneg (by omega : 0<d) (q : Space d) hq
    linarith
  have hb := value_add_le_of_hessian_nonpos (by omega) x.1 (potential hd x) q hu hq hfirst hsecond
  have hm : MeanZero (potential hd x) := mean_reconstruction _
  have hmq : MeanZero (potential hd x+(q : Space d)) := by
    change mean d (potential hd x+(q : Space d))=0
    rw [map_add,show mean d (potential hd x)=0 from hm,show mean d (q : Space d)=0 from q.property.1]
    simp
  rw [value_eq_dual (by omega) _ _ hmq,value_eq_dual (by omega) _ _ hm]
  exact EReal.coe_le_coe_iff.mpr hb

#print axioms exists_complement_energy_bound
end BecknerOnofri.HighDim.LocalEleven.ContinuousEnergy
