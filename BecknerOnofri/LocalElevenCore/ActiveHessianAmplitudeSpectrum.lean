import BecknerOnofri.LocalElevenCore.ActiveHessianTransverse
import BecknerOnofri.EquicorrelatedEigenvalueIdentification

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

/-- Exact matrix and analytic eigenvalue germs for every nonempty support,
including a one-element support. -/
theorem exists_active_amplitude_matrix_spectrum {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∃ R T : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ AnalyticAt ℝ T 0 ∧
      R 0=2*quarticA d+quarticB d*((I.card:ℝ)-1) ∧ T 0=2*quarticA d-quarticB d ∧
      ((fun t => R t-R 0) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      ((fun t => T t-T 0) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),0<t →
        activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))=
          EquicorrelatedSpectrum.operator (T t) ((R t-T t)/(I.card:ℝ))) := by
  letI : Nonempty I := ⟨⟨j,hj⟩⟩
  obtain ⟨R,hR,hR0,hRo,hRe⟩ := exists_active_radial_eigenvalue hd I j hj
  have hp : ∃ a b : Fin d,a≠b ∧ (Subsingleton I ∨ (a∈I ∧ b∈I)) := by
    cases subsingleton_or_nontrivial I with
    | inl hs => exact ⟨⟨0,by omega⟩,⟨1,by omega⟩,by simp,Or.inl hs⟩
    | inr hn =>
        letI := hn
        obtain ⟨a,b,hab⟩ := exists_pair_ne I
        exact ⟨a.val,b.val,(fun h => hab (Subtype.ext h)),Or.inr ⟨a.property,b.property⟩⟩
  obtain ⟨a,b,hab,hcase⟩ := hp
  obtain ⟨T,hT,hT0,hTo,hTe⟩ := exists_active_transverse_coefficient hd I j hj a b hab
  refine ⟨R,T,hR,hT,hR0,hT0,?_,?_,?_⟩
  · simpa only [hR0] using hRo
  · simpa only [hT0] using hTo
  · filter_upwards [hRe,hTe,(squaredBranchInput_tendsto hd I j hj).eventually
      (activeHessian_equicorrelated hd I ⟨j,hj⟩)] with t hr ht hm hpos
    have hrad := hr hpos
    rcases hcase with hsub | ⟨ha,hb⟩
    · letI := hsub
      simpa only [Fintype.card_coe] using
        EquicorrelatedSpectrum.eq_operator_of_radial_subsingleton _ (R t) (T t) hrad
    · obtain ⟨α,β,hM⟩ := hm (fun k hk => by
        simpa only [squaredBranchInput,realLine_apply,if_pos hk] using sq_pos_of_pos hpos)
        (fun k hk l hl => by simp only [squaredBranchInput,realLine_apply,if_pos hk,if_pos hl])
      change activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))=_ at hM
      have htrans := ht hpos ha hb
      rw [hM] at hrad htrans ⊢
      simpa only [Fintype.card_coe] using
        EquicorrelatedSpectrum.operator_eq_of_radial_and_row_difference α β (R t) (T t)
          (⟨a,ha⟩ : I) ⟨b,hb⟩ (fun h => hab (congrArg Subtype.val h)) hrad htrans

/-- Both eigenvalues of the genuine active Hessian are strictly negative,
and their eigenspaces have exactly the manuscript's dimensions. -/
theorem exists_active_amplitude_spectrum {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (j : Fin d) (hj : j∈I) :
    ∃ R T : ℝ → ℝ,AnalyticAt ℝ R 0 ∧ AnalyticAt ℝ T 0 ∧
      R 0=2*quarticA d+quarticB d*((I.card:ℝ)-1) ∧ T 0=2*quarticA d-quarticB d ∧
      ((fun t => R t-R 0) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      ((fun t => T t-T 0) =O[𝓝 (0:ℝ)] (fun t => ‖t‖^2)) ∧
      (∀ᶠ t in 𝓝 (0:ℝ),0<t → R t<0 ∧ T t<0 ∧ R t≠T t ∧
        activeHessian hd I (SubsetDiagonal.parameter hd I j hj t) (realLine I (t^2))=
          EquicorrelatedSpectrum.operator (T t) ((R t-T t)/(I.card:ℝ)) ∧
        Module.finrank ℝ ((activeHessian hd I (SubsetDiagonal.parameter hd I j hj t)
          (realLine I (t^2))).eigenspace (R t))=1 ∧
        Module.finrank ℝ ((activeHessian hd I (SubsetDiagonal.parameter hd I j hj t)
          (realLine I (t^2))).eigenspace (T t))=I.card-1) := by
  letI : Nonempty I := ⟨⟨j,hj⟩⟩
  obtain ⟨R,T,hR,hT,hR0,hT0,hRo,hTo,he⟩ := exists_active_amplitude_matrix_spectrum hd I j hj
  have hRneg : R 0<0 := by
    rw [hR0]
    have hc := SubsetDiagonal.coefficient_pos hd I ⟨j,hj⟩
    dsimp only [SubsetDiagonal.coefficient] at hc
    linarith
  have hTneg : T 0<0 := by
    rw [hT0]
    have ha := LocalQuartic.quarticA_negative hd
    have hb := LocalQuartic.quarticB_positive hd
    linarith
  have hdiff : 0<R 0-T 0 := by
    rw [hR0,hT0]
    have hn : (0:ℝ)<I.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨j,hj⟩)
    have hb := mul_pos hn (LocalQuartic.quarticB_positive hd)
    nlinarith
  refine ⟨R,T,hR,hT,hR0,hT0,hRo,hTo,?_⟩
  filter_upwards [he,hR.continuousAt.tendsto.eventually (gt_mem_nhds hRneg),
    hT.continuousAt.tendsto.eventually (gt_mem_nhds hTneg),
    (hR.continuousAt.sub hT.continuousAt).tendsto.eventually (lt_mem_nhds hdiff)]
      with t he hr ht hdiff hpos
  change 0<R t-T t at hdiff
  have hne : R t≠T t := by linarith
  refine ⟨hr,ht,hne,he hpos,?_⟩
  rw [he hpos]
  have h := EquicorrelatedSpectrum.eigenvalue_multiplicities_of_radial_transverse (ι := I) (R t) (T t) hne
  rw [Fintype.card_coe] at h
  exact h

#print axioms exists_active_amplitude_spectrum
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
