import BecknerOnofri.LocalElevenCore.SubsetCubic
import BecknerOnofri.AnalyticPitchforkPositive
import BecknerOnofri.LocalElevenCore.GraphRegularity
import BecknerOnofri.LocalElevenCore.GraphCritical
import BecknerOnofri.LocalElevenCore.EulerEquation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

/-- All scalar pitchfork hypotheses are discharged for the actual Euler residual. -/
def pitchforkData {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I) :
    AnalyticPitchfork.Data where
  residual := residual hd I j
  coefficient := coefficient I
  analytic := residual_analytic hd I j
  axis := residual_axis hd I j
  derivative_axis := residual_derivative_axis hd I j hj
  odd := residual_odd hd I j
  cubic := residual_cubic hd I j hj

def parameter {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I) :=
  AnalyticPitchfork.parameter (pitchforkData hd I j hj)

def branchPotential {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (j : Fin d) (hj : j∈I)
    (t : ℝ) : Space d := ReducedEquation.potential hd (parameter hd I j hj t,line I t)

theorem branch_coordinates_tendsto {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    Tendsto (fun t : ℝ => (parameter hd I j hj t,line I t)) (𝓝 0)
      (𝓝 (1,(0 : Coordinates d))) :=
  (embedding_tendsto I).comp (AnalyticPitchfork.parameter_pair_tendsto (pitchforkData hd I j hj))

theorem branchPotential_analytic {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) : AnalyticAt ℝ (branchPotential hd I j hj) 0 := by
  have hi := (AnalyticPitchfork.parameter_analytic (pitchforkData hd I j hj)).prod
    ((line I).analyticAt 0)
  have ho : AnalyticAt ℝ (ReducedEquation.potential hd)
      (parameter hd I j hj 0,line I 0) := by
    simpa only [parameter,AnalyticPitchfork.parameter_base,map_zero] using
      ReducedEquation.potential_analytic hd
  exact ho.comp (f := fun t => (parameter hd I j hj t,line I t)) hi

@[simp] theorem branchPotential_coordinates {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) (t : ℝ) :
    coordinates d (branchPotential hd I j hj t)=line I t := by
  simp only [branchPotential,ReducedEquation.potential,reconstruction_apply,map_add,
    coordinates_assembly,ReducedEquation.coordinates_complement,add_zero]

@[simp] theorem branchPotential_mean {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) (t : ℝ) : mean d (branchPotential hd I j hj t)=0 :=
  mean_reconstruction _

theorem parameter_reduced_zero {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ t in 𝓝 (0:ℝ), ReducedEquation.reduced hd (parameter hd I j hj t,line I t)=0 := by
  let D := pitchforkData hd I j hj
  filter_upwards [(AnalyticPitchfork.parameter_pair_tendsto D).eventually
    (AnalyticPitchfork.residual_eq_mul_quotient D),AnalyticPitchfork.parameter_solves D,
    (AnalyticPitchfork.parameter_pair_tendsto D).eventually (reduced_line hd I j hj)]
    with t hf hq hr
  have hz : residual hd I j (parameter hd I j hj t,t)=0 := by
    change D.residual (AnalyticPitchfork.parameter D t,t)=0
    rw [hf,hq,mul_zero]
  change ReducedEquation.reduced hd (parameter hd I j hj t,line I t)=
    line I (residual hd I j (parameter hd I j hj t,t)) at hr
  simpa only [hz,map_zero] using hr

theorem branchPotential_properties {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∀ᶠ t in 𝓝 (0:ℝ), SmoothOnTorus (branchPotential hd I j hj t) ∧
      (∀ s : ℝ, InSobolev s (branchPotential hd I j hj t)) ∧
      InCriticalSobolev (branchPotential hd I j hj t) ∧
      ReducedEquation.full d (parameter hd I j hj t) (branchPotential hd I j hj t)=0 := by
  have ht := branch_coordinates_tendsto hd I j hj
  filter_upwards [ht.eventually (GraphRegularity.potential_regular hd),
    ht.eventually (GraphCritical.potential_inCriticalSobolev hd),
    ht.eventually (ReducedEquation.graph_full_iff_reduced hd),
    parameter_reduced_zero hd I j hj] with t hreg hcrit hf hr
  exact ⟨hreg.1,hreg.2,hcrit,hf.mpr hr⟩

#print axioms branchPotential_properties
end BecknerOnofri.HighDim.LocalEleven.SubsetDiagonal
