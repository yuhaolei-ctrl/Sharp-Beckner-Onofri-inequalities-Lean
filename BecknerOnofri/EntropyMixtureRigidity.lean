module

public import BecknerOnofri.EntropyTailBudget
public import BecknerOnofri.GenericCosineRepresentation
public import BecknerOnofri.BranchDefinitions

@[expose] public section

/-! The zero-first-moment rigidity argument (5.55) for the actual countable
cosine mixture. The outer coordinate indices need not be independent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace BecknerOnofri.HighDim.EntropyMixtureRigidity
open Legacy.TorusEndpoint Legacy.BecknerOnofri Legacy.D10

theorem component_axis {d : ℕ} (N : Fin d → ℕ) (i : Fin d) :
    RandomRectangles.componentCoeff N (axisFrequency i)=
      (N i:ℝ)/((N i:ℝ)+1) := by
  unfold RandomRectangles.componentCoeff binomialProduct axisFrequency
  have he (j : Fin d) : binomialCoeffReal (N j) ((if j=i then (1:ℤ) else 0).natAbs)=
      if j=i then binomialCoeffReal (N i) 1 else 1 := by
    split_ifs with h
    · subst j
      simp
    · simp [RandomRectangles.coeff_zero]
  simp_rw [he]
  simp [EntropyTail.first_coefficient]

theorem mixture_uniform_of_axes_zero {d : ℕ} (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n,0≤w n) (hm : HasSum w 1)
    (haxis : ∀ i : Fin d,densityFourier (CosineMixtureApproximation.rho w N) (axisFrequency i)=0) :
    CosineMixtureApproximation.rho w N=(fun _ => 1) := by
  have hz (i : Fin d) : (∑' n,w n*RandomRectangles.componentCoeff (N n) (axisFrequency i))=0 := by
    have h := haxis i
    rw [CosineMixtureTransfer.rho_fourier w N hw hm.summable] at h
    exact_mod_cast h
  have hindex (n : ℕ) (hn : 0<w n) : N n=0 := by
    funext i
    have hh := (CosineMixtureTransfer.summable_mixture_coeff w N hw hm.summable (axisFrequency i)).le_tsum
      n (fun m _ => mul_nonneg (hw m) (RandomRectangles.componentCoeff_nonneg _ _))
    rw [hz i,component_axis] at hh
    have hnn : 0≤(N n i:ℝ)/((N n i:ℝ)+1) := by positivity
    have he : (N n i:ℝ)/((N n i:ℝ)+1)=0 := by nlinarith
    have he' : (N n i:ℝ)=0 := (div_eq_zero_iff).mp he |>.resolve_right (by positivity)
    exact_mod_cast he'
  funext x
  unfold CosineMixtureApproximation.rho
  calc
    _ = ∑' n,w n := by
      apply tsum_congr
      intro n
      by_cases hn : w n=0
      · simp [hn]
      · have he := hindex n (lt_of_le_of_ne (hw n) (Ne.symm hn))
        rw [he]
        simp [show (0 : Fin d → ℕ)=(fun _ => 0) from rfl]
    _ = 1 := hm.tsum_eq

/-- The exact implication applies directly to the positive-mixture interface
already established by variational selection. -/
theorem positive_mixture_uniform {d : ℕ} {f : Torus d → ℝ}
    (hf : GenericCosineRepresentation.HasPositiveCosineMixture f)
    (haxis : ∀ i : Fin d,densityFourier f (axisFrequency i)=0) : f=(fun _ => 1) := by
  obtain ⟨w,N,hw,hm,_,rfl⟩ := hf
  exact mixture_uniform_of_axes_zero w N hw hm haxis

#print axioms positive_mixture_uniform
end BecknerOnofri.HighDim.EntropyMixtureRigidity
