import BecknerOnofri.LocalElevenCore.SquaredHessianRowDifference
import BecknerOnofri.LocalElevenCore.SquaredHessianSymmetry
import BecknerOnofri.EquicorrelatedRecognition

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
open AmplitudeLinearization ActiveAmplitudeFactor

/-- Active coordinates are extended by zero before differentiating the actual energy. -/
def activeExtend {d : ℕ} (I : Finset (Fin d)) : (I → ℝ) →L[ℝ] Amplitudes d :=
  ContinuousLinearMap.pi (fun i => if hi : i∈I then ContinuousLinearMap.proj ⟨i,hi⟩ else 0)

@[simp] theorem activeExtend_apply {d : ℕ} (I : Finset (Fin d)) (v : I → ℝ) (i : Fin d) :
    activeExtend I v i=if hi : i∈I then v ⟨i,hi⟩ else 0 := by
  simp only [activeExtend,ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

@[simp] theorem activeExtend_active {d : ℕ} (I : Finset (Fin d)) (v : I → ℝ) (i : I) :
    activeExtend I v i=v i := by simp

theorem activeExtend_single {d : ℕ} (I : Finset (Fin d)) (j : I) :
    activeExtend I (Pi.single j 1)=Pi.single j.val 1 := by
  funext i
  by_cases hi : i∈I
  · simp only [activeExtend_apply,dif_pos hi,Pi.single_apply]
    by_cases hij : i=j.val
    · subst i; simp
    · have hsub : (⟨i,hi⟩ : I)≠j := fun h => hij (congrArg Subtype.val h)
      simp [hij,hsub]
  · have hij : i≠j.val := fun h => hi (h ▸ j.property)
    simp [hi,hij]

/-- Restriction of the genuine squared-amplitude Hessian to the active support. -/
def activeHessian {d : ℕ} (hd : 11≤d) (I : Finset (Fin d)) (μ : ℝ) (r : Amplitudes d) :
    Module.End ℝ (I → ℝ) :=
  (LinearMap.pi (fun i : I => LinearMap.proj i.val)).comp
    ((hessianMap hd I μ r).toLinearMap.comp (activeExtend I).toLinearMap)

@[simp] theorem activeHessian_apply {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (μ : ℝ) (r : Amplitudes d) (v : I → ℝ) (i : I) :
    activeHessian hd I μ r v i=hessianMap hd I μ r (activeExtend I v) i := rfl

/-- The actual active Hessian is a scalar matrix plus a multiple of the
all-ones matrix on the equal-positive-amplitude locus. Both its symmetry and
its row identities were derived from the actual reduced energy. -/
theorem activeHessian_equicorrelated {d : ℕ} (hd : 11≤d) (I : Finset (Fin d))
    (hI : I.Nonempty) :
    ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),
      (∀ i∈I,0<x.2 i) → (∀ i∈I,∀ j∈I,x.2 i=x.2 j) →
      ∃ a b : ℝ,activeHessian hd I x.1 x.2=EquicorrelatedSpectrum.operator a b := by
  letI : Nonempty I := ⟨⟨hI.choose,hI.choose_spec⟩⟩
  have hp (i j : I) : ∀ᶠ x : ℝ × Amplitudes d in 𝓝 (1,0),
      (∀ k∈I,0<x.2 k) → x.2 i=x.2 j →
      ∃ c : ℝ,∀ v : I → ℝ,
        activeHessian hd I x.1 x.2 v i-activeHessian hd I x.1 x.2 v j=c*(v i-v j) := by
    by_cases hij : i=j
    · subst j
      exact Filter.Eventually.of_forall (fun _ _ _ => ⟨0,by intro v; simp⟩)
    · have hval : i.val≠j.val := fun h => hij (Subtype.ext h)
      obtain ⟨H,hH,_,he⟩ := exists_nonzero_squared_difference_factor hd i.val j.val hval
      filter_upwards [hessian_row_difference hd I i.val j.val i.property j.property hH
        (he.mono (fun _ h => h.2))] with x hx hr heq
      refine ⟨-(H (x.1,sqrtLift I x.2)/x.1),?_⟩
      intro v
      simpa only [activeHessian_apply,activeExtend_active] using hx hr heq (activeExtend I v)
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))
  filter_upwards [hessian_entries_symmetric hd I,hall] with x hs hr hpos heq
  apply EquicorrelatedSpectrum.exists_operator_of_row_differences
  · intro i j
    simpa only [activeHessian_apply,activeExtend_single] using hs hpos i.val j.val
  · intro i j
    exact hr i j hpos (heq i.val i.property j.val j.property)

#print axioms activeHessian_equicorrelated
end BecknerOnofri.HighDim.LocalEleven.SquaredReducedEnergy
