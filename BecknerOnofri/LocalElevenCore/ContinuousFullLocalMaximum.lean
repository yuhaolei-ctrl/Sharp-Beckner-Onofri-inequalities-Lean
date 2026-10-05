module

public import BecknerOnofri.LocalElevenCore.ComplexReducedLocalMaximum
public import BecknerOnofri.LocalElevenCore.ComplementEnergyMaximum

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven
open ContinuousGibbs ContinuousFirstShell ContinuousComplement ReducedEquation
open DiagonalScalarBranch ReducedCubicExpansion ReducedEnergyGradient ContinuousEnergy

theorem potential_coordinates {d : ℕ} (hd : 11≤d) (x : ℝ × Coordinates d) :
    coordinates d (potential hd x)=x.2 := coordinates_reconstruction _

/-- The full physical energy is locally maximal on the actual continuous,
mean-zero critical-Sobolev domain, including all complementary directions. -/
theorem continuous_full_local_maximum {d : ℕ} (hd : 11≤d) :
    ∀ᶠ μ in 𝓝[>] (1:ℝ),
      ∀ᶠ v : Space d in 𝓝 (potential hd (μ,realDiagonal d (amplitude hd μ))),
        InCriticalSobolev v → MeanZero v → dualFunctional (μ*spectralThreshold d) v≤
          dualFunctional (μ*spectralThreshold d) (potential hd (μ,realDiagonal d (amplitude hd μ))) := by
  obtain ⟨ε,hε,hcomp⟩ := exists_complement_energy_bound hd
  have ht : Tendsto (fun μ => (μ,realDiagonal d (amplitude hd μ)))
      (𝓝[>] (1:ℝ)) (𝓝 (1,(0 : Coordinates d))) := by
    have hz := ((realDiagonal d).continuous.tendsto 0).comp (amplitude_tendsto hd)
    simp only [map_zero] at hz
    exact (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hz
  filter_upwards [RealReducedEnergy.diagonal_complex_isLocalMax hd,
    ht.eventually hcomp.eventually_nhds,
    ht.eventually (potential_analytic hd).eventually_analyticAt,
    ht.eventually (GraphCritical.potential_inCriticalSobolev hd).eventually_nhds]
    with μ hmax hcomp ha hcrit
  let z := realDiagonal d (amplitude hd μ)
  let u := potential hd (μ,z)
  have hcoord : coordinates d u=z := potential_coordinates hd _
  have hinc : Tendsto (fun v : Space d => (μ,coordinates d v)) (𝓝 u) (𝓝 (μ,z)) := by
    have hc : Continuous (fun v : Space d => (μ,coordinates d v)) :=
      continuous_const.prodMk (coordinates d).continuous
    have h := hc.tendsto u
    simpa only [hcoord] using h
  have hcoords : Tendsto (coordinates d) (𝓝 u) (𝓝 z) := by
    simpa only [hcoord] using (coordinates d).continuous.tendsto u
  have hQ : ∀ᶠ v : Space d in 𝓝 u,‖v-potential hd (μ,coordinates d v)‖<ε := by
    have hpot := ha.continuousAt.tendsto.comp hinc
    change Tendsto (fun v : Space d => potential hd (μ,coordinates d v)) (𝓝 u) (𝓝 u) at hpot
    have hzero : Tendsto (fun v : Space d => v-potential hd (μ,coordinates d v)) (𝓝 u) (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,sub_self] using
        tendsto_id.sub hpot
    have hn : Tendsto (fun v : Space d => ‖v-potential hd (μ,coordinates d v)‖) (𝓝 u) (𝓝 0) := by
      simpa only [norm_zero] using hzero.norm
    exact hn.eventually (gt_mem_nhds hε)
  filter_upwards [hQ,hinc.eventually hcomp,hinc.eventually hcrit,hcoords.eventually hmax]
    with v hQ hcomp hcrit hmax
  intro hv hm
  let g := potential hd (μ,coordinates d v)
  have hgm : MeanZero g := mean_reconstruction _
  have hmem : v-g∈complement d := by
    apply (mem_complement_iff _).mpr
    constructor
    · rw [map_sub,show mean d v=0 from hm,show mean d g=0 from hgm,sub_self]
    · intro i
      have hc : coordinates d (v-g)=0 := by rw [map_sub,potential_coordinates,sub_self]
      exact congrFun hc i
  let q : complement d := ⟨v-g,hmem⟩
  have hq : InCriticalSobolev (q : Space d) :=
    FullHessianDecomposition.critical_sub v g hv hcrit
  have hsum : g+(q : Space d)=v := by dsimp [q]; abel
  have hc := hcomp q hq hQ
  change dualFunctional (μ*spectralThreshold d) (g+(q : Space d))≤dualFunctional (μ*spectralThreshold d) g at hc
  rw [hsum] at hc
  apply hc.trans
  have hum : MeanZero u := mean_reconstruction _
  rw [value_eq_dual (by omega) _ g hgm,value_eq_dual (by omega) _ u hum]
  apply EReal.coe_le_coe_iff.mpr
  change (dualFunctional (μ*spectralThreshold d) g).toReal≤
    (dualFunctional (μ*spectralThreshold d) u).toReal at hmax
  simpa only [value_eq_dual (by omega) _ g hgm,value_eq_dual (by omega) _ u hum,EReal.toReal_coe] using hmax

#print axioms continuous_full_local_maximum
end BecknerOnofri.HighDim.LocalEleven
