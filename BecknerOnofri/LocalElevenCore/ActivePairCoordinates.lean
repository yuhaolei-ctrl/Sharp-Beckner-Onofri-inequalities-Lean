import BecknerOnofri.LocalElevenCore.ActiveFactorReflection

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
open AmplitudeLinearization
abbrev Input (d : ℕ) := ℝ × Amplitudes d

def pairInput {d : ℕ} (i j : Fin d) : (Input d × ℝ) × ℝ →L[ℝ] Input d :=
  let P := (ContinuousLinearMap.fst ℝ (Input d) ℝ).comp
    (ContinuousLinearMap.fst ℝ (Input d × ℝ) ℝ)
  let u := (ContinuousLinearMap.snd ℝ (Input d) ℝ).comp
    (ContinuousLinearMap.fst ℝ (Input d × ℝ) ℝ)
  let v := ContinuousLinearMap.snd ℝ (Input d × ℝ) ℝ
  ((ContinuousLinearMap.fst ℝ ℝ (Amplitudes d)).comp P).prod
    (ContinuousLinearMap.pi (fun k => if k=i then u else if k=j then v else (coordinate d k).comp P))

@[simp] theorem pairInput_apply {d : ℕ} (i j : Fin d) (x : (Input d × ℝ) × ℝ) :
    pairInput i j x=(x.1.1.1,fun k => if k=i then x.1.2 else if k=j then x.2 else x.1.1.2 k) := by
  apply Prod.ext
  · rfl
  · funext k
    simp only [pairInput,ContinuousLinearMap.prod_apply,ContinuousLinearMap.pi_apply]
    split_ifs <;> rfl

@[simp] theorem pairInput_base {d : ℕ} (i j : Fin d) : pairInput i j (((1,0),0),0)=(1,0) := by
  rw [pairInput_apply]
  apply Prod.ext
  · rfl
  funext k
  dsimp only
  split_ifs <;> rfl

theorem pairInput_tendsto {d : ℕ} (i j : Fin d) :
    Tendsto (pairInput i j) (𝓝 (((1,0),0),0)) (𝓝 (1,0)) := by
  simpa only [pairInput_base] using (pairInput i j).continuous.tendsto (((1,0),0),0)

theorem pairInput_swap {d : ℕ} {i j : Fin d} (hij : i≠j) (x : (Input d × ℝ) × ℝ) :
    pairInput i j ((x.1.1,x.2),x.1.2)=permuteInput (Equiv.swap i j) (pairInput i j x) := by
  simp only [pairInput_apply,permuteInput_apply]
  apply Prod.ext
  · rfl
  funext k
  dsimp only
  by_cases hki : k=i
  · subst k; simp [hij,hij.symm]
  by_cases hkj : k=j
  · subst k; simp [hij,hij.symm]
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  simp [hki,hkj]

theorem pairInput_flip {d : ℕ} {i j : Fin d} (hij : i≠j) (x : (Input d × ℝ) × ℝ) :
    pairInput i j (x.1,-x.2)=flipInput j (pairInput i j x) := by
  simp only [pairInput_apply,flipInput_apply]
  apply Prod.ext
  · rfl
  funext k
  dsimp only
  by_cases hki : k=i
  · subst k; simp [hij,hij.symm]
  by_cases hkj : k=j
  · subst k; simp [hij,hij.symm]
  simp [hki,hkj]

def extractPair {d : ℕ} (i j : Fin d) : Input d →L[ℝ] (Input d × ℝ) × ℝ :=
  ((ContinuousLinearMap.id ℝ (Input d)).prod (coordinate d i)).prod (coordinate d j)

@[simp] theorem extractPair_apply {d : ℕ} (i j : Fin d) (x : Input d) :
    extractPair i j x=((x,x.2 i),x.2 j) := rfl

@[simp] theorem pairInput_extractPair {d : ℕ} (i j : Fin d) (x : Input d) :
    pairInput i j (extractPair i j x)=x := by
  rw [extractPair_apply,pairInput_apply]
  apply Prod.ext
  · rfl
  funext k
  dsimp only
  split_ifs with hi hj
  · subst k; rfl
  · subst k; rfl
  · rfl

#print axioms pairInput_swap
end BecknerOnofri.HighDim.LocalEleven.ActiveAmplitudeFactor
