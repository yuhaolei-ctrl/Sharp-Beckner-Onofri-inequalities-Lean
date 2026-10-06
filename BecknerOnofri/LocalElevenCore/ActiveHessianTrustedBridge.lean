module

public import BecknerOnofri.ActiveSquaredHessianDefinitions
public import BecknerOnofri.LocalElevenCore.ActiveHessianPhysicalSpectrum
public import BecknerOnofri.LocalElevenCore.SubsetEnergyFamily

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor ContinuousGibbs ContinuousFirstShell
open LocalReductionStatement
theorem trusted_coordinates {d : ℕ} (I : Finset (Fin d)) (r : Amplitudes d) :
    ActiveSquaredHessian.coordinates I r=RescaledReducedEquation.realCoordinates d (sqrtLift I r) := by
  funext i
  by_cases hi : i∈I <;> simp [ActiveSquaredHessian.coordinates,
    RescaledReducedEquation.realCoordinates_apply,sqrtLift,hi]

theorem trusted_potential {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) (r : Amplitudes d) :
    ActiveSquaredHessian.potential (GreenLocalBranch.correction hd) I μ r=
      ReducedEquation.potential hd (μ,RescaledReducedEquation.realCoordinates d (sqrtLift I r)) := by
  simp only [ActiveSquaredHessian.potential,trusted_coordinates,ReducedEquation.potential]

theorem trusted_energy {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) :
    ActiveSquaredHessian.energy (GreenLocalBranch.correction hd) I μ=value hd I μ := by
  funext r
  rw [ActiveSquaredHessian.energy,trusted_potential]
  rfl

theorem trusted_squaredDiagonal {d : ℕ} (I : Finset (Fin d)) (r : ℝ) :
    ActiveSquaredHessian.squaredDiagonal I r=realLine I r := by
  funext i
  simp only [ActiveSquaredHessian.squaredDiagonal,realLine_apply]

/-- Identification of the independently defined trusted Hessian with the
matrix whose spectrum was proved from the actual Euler coordinate factors. -/
theorem trusted_hessian {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),(∀ i∈I,0<x.2 i) →
      ActiveSquaredHessian.hessian (GreenLocalBranch.correction hd) I x.1 x.2=
        activeHessian hd I x.1 x.2 := by
  filter_upwards [second_fderiv_value hd I] with x hx hr
  apply LinearMap.ext
  intro v
  funext i
  change fderiv ℝ (fun r => fderiv ℝ (ActiveSquaredHessian.energy
    (GreenLocalBranch.correction hd) I x.1) r) x.2
      (activeExtend I v) (Pi.single i.val 1)=hessianMap hd I x.1 x.2 (activeExtend I v) i
  rw [trusted_energy,hx hr]
  simp only [ContinuousLinearMap.comp_apply,RealReducedEnergy.dotDual_apply,
    Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem supported_profile_canonical {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) {r : ℝ → ℝ} (hr : AnalyticAt ℝ r 0) (hr0 : r 0=0)
    (hp : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧
      SubsetDiagonal.parameter hd I j hj (Real.sqrt (r δ))=1/(1-δ)) :
    SupportedProfile d I r (fun δ => SubsetDiagonal.branchPotential hd I j hj (Real.sqrt (r δ))) := by
  let U : ℝ → Space d := fun δ => SubsetDiagonal.branchPotential hd I j hj (Real.sqrt (r δ))
  have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [hr0,Real.sqrt_zero] using hr.continuousAt.sqrt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hb0 : SubsetDiagonal.branchPotential hd I j hj 0=0 := by
    simp [SubsetDiagonal.branchPotential,SubsetDiagonal.parameter,AnalyticPitchfork.parameter_base,
      ReducedEquation.potential,GreenLocalBranch.correction_base]
  refine ⟨?_,?_⟩
  · simpa only [hb0,Function.comp_def] using
      (SubsetDiagonal.branchPotential_analytic hd I j hj).continuousAt.tendsto.comp ht
  · filter_upwards [hp,ht.eventually (SubsetDiagonal.branchPotential_properties hd I j hj)] with δ hp hb
    have hf : ReducedEquation.full d (1/(1-δ)) (U δ)=0 := by
      simpa only [U,← hp.2] using hb.2.2.2
    have hs := (ReducedEquation.full_zero_iff_stationary (by omega) _ _).mp hf
    have hcoeff (k : Fin d) : fourierCoeff (U δ) (axisFrequency k)=
        if k∈I then ((Real.sqrt (r δ)):ℂ) else 0 := by
      rw [← coefficient_eq_fourierCoeff]
      simpa only [ContinuousFirstShell.coordinates,SubsetDiagonal.line_apply,U,
        ContinuousLinearMap.pi_apply] using
          congrFun (SubsetDiagonal.branchPotential_coordinates hd I j hj (Real.sqrt (r δ))) k
    refine ⟨hp.1,hb.1,hb.2.1,hb.2.2.1,hs.1,hs.2,hcoeff,?_⟩
    intro k
    rw [hcoeff]
    have hn : (Real.sqrt (r δ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp.1).ne'
    by_cases hk : k∈I <;> simp [hk,hn]

/-- Full physical-parameter active Hessian assertion, with one squared
amplitude for all supports of a given size and the same genuine graph. -/
theorem active_squared_hessian_family {d : ℕ} (hd : 11≤d) : ActiveSquaredHessian.Family d := by
  refine ⟨GreenLocalBranch.correction hd,GreenLocalBranch.correction_analytic hd,
    GreenLocalBranch.correction_base hd,GreenLocalBranch.correction_derivative_zero hd,
    GreenLocalBranch.correction_solves hd,GreenLocalBranch.correction_unique hd,?_,?_⟩
  · filter_upwards [GraphCritical.potential_inCriticalSobolev hd,GraphRegularity.potential_regular hd]
      with x hc hr
    exact ⟨hc,hr⟩
  · intro n hn hnd
    obtain ⟨J,hJsub,hJcard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin d))) (by simpa using hnd)
    have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨j,hj⟩ := hJ
    let D := SubsetDiagonal.pitchforkData hd J j hj
    obtain ⟨r,hr,hr0,hrd,he,hp⟩ := AnalyticPitchfork.exists_positive_squared_amplitude D
      (SubsetDiagonal.coefficient_pos hd J ⟨j,hj⟩)
    have hc : D.coefficient=supportCoefficient d n := by
      simp only [D,SubsetDiagonal.pitchforkData,SubsetDiagonal.coefficient,supportCoefficient,hJcard]
    refine ⟨r,hr,hr0,?_,?_,?_⟩
    · simpa only [hc] using hrd
    · simpa only [hc] using he
    · intro I hIcard
      have hI : I.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨i,hi⟩ := hI
      have ht : Tendsto (fun δ => Real.sqrt (r δ)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa only [hr0,Real.sqrt_zero] using hr.continuousAt.sqrt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      have hpI : ∀ᶠ δ in 𝓝[>] (0:ℝ),0<r δ ∧
          SubsetDiagonal.parameter hd I i hi (Real.sqrt (r δ))=1/(1-δ) := by
        filter_upwards [hp,ht.eventually (SubsetDiagonal.parameter_eq_of_card_eq hd J I j i hj hi
          (hJcard.trans hIcard.symm))] with δ hp heq
        exact ⟨hp.1,heq.symm.trans hp.2⟩
      obtain ⟨R,T,hRo,hTo,hSp⟩ := active_physical_spectrum_of_parameter hd I i hi hr hr0 hpI
      refine ⟨fun δ => SubsetDiagonal.branchPotential hd I i hi (Real.sqrt (r δ)),R,T,
        supported_profile_canonical hd I i hi hr hr0 hpI,?_,hRo,hTo,?_⟩
      · filter_upwards [hpI] with δ hp
        rw [SubsetDiagonal.branchPotential,hp.2,trusted_potential,trusted_squaredDiagonal]
        have hs : sqrtLift I (realLine I (r δ))=realLine I (Real.sqrt (r δ)) := by
          funext k
          by_cases hk : k∈I <;> simp [sqrtLift,hk]
        rw [hs,realCoordinates_realLine]
      · have hinput : Tendsto (fun δ : ℝ => (1/(1-δ),realLine I (r δ)))
            (𝓝[>] (0:ℝ)) (𝓝 (1,0)) := by
          have hμ : ContinuousAt (fun δ : ℝ => 1/(1-δ)) 0 :=
            continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
          have hline : ContinuousAt (fun δ => realLine I (r δ)) 0 :=
            (realLine I).continuous.continuousAt.comp hr.continuousAt
          simpa only [hr0,map_zero,sub_zero,div_one] using
            (hμ.prodMk hline).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        filter_upwards [hSp,hinput.eventually (trusted_hessian hd I),hpI] with δ hs hh hp
        have hh' := hh (fun k hk => by simpa only [realLine_apply,if_pos hk] using hp.1)
        rw [trusted_squaredDiagonal,hh']
        refine ⟨hs.1,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
        intro v k
        rw [hs.2.2.2.1]
        rfl

#print axioms active_squared_hessian_family
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
