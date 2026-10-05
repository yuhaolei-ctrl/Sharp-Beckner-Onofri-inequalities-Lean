module

public import BecknerOnofri.SobolevCriticalInclusion
public import BecknerOnofri.FullHessianDecomposition

@[expose] public section

noncomputable section
namespace BecknerOnofri.HighDim

theorem inSobolev_sub {d : ℕ} {s : ℝ} {f g : Torus d → ℝ}
    (hf : InSobolev s f) (hg : InSobolev s g) : InSobolev s (f-g) := by
  refine ⟨hf.1.sub hg.1,?_⟩
  apply ((hf.2.add hg.2).mul_left 2).of_nonneg_of_le
    (fun k => by unfold sobolevTerm; positivity)
  intro k
  have hw : 0≤(1+(2*Real.pi*frequencyLength k)^2)^s :=
    Real.rpow_nonneg (by positivity) _
  have hn : ‖fourierCoeff f k-fourierCoeff g k‖^2≤
      2*(‖fourierCoeff f k‖^2+‖fourierCoeff g k‖^2) := by
    have h := norm_sub_le (fourierCoeff f k) (fourierCoeff g k)
    nlinarith [norm_nonneg (fourierCoeff f k-fourierCoeff g k),
      norm_nonneg (fourierCoeff f k),norm_nonneg (fourierCoeff g k),
      sq_nonneg (‖fourierCoeff f k‖-‖fourierCoeff g k‖)]
  simp only [sobolevTerm,FullHessianDecomposition.fourierCoeff_sub f g hf.1 hg.1]
  nlinarith [mul_le_mul_of_nonneg_left hn hw]

/-- The trusted Morse--Bott interface indeed gives a maximum over all mean-zero
H^s competitors; its critical-domain and difference-membership fields are redundant. -/
theorem FullModeMorseBott.localMaximum_sobolev {d : ℕ} {β : ℝ} {u : Torus d → ℝ}
    (hu : FullModeMorseBott β u) (s : ℝ) (hs : (d:ℝ)/2<s) :
    ∃ r : ℝ,0<r ∧ ∀ v : Torus d → ℝ,InSobolev s v → MeanZero v →
      sobolevNorm s (fun x => v x-u x)<r → dualFunctional β v≤dualFunctional β u := by
  obtain ⟨r,hr,h⟩ := hu.localMaximum s hs
  refine ⟨r,hr,?_⟩
  intro v hv hm hn
  have hs0 : 0≤s := le_trans (by positivity : (0:ℝ)≤(d:ℝ)/2) hs.le
  exact h v hv (inCriticalSobolev_of_inSobolev hs.le hv) hm
    (inSobolev_sub hv (hu.sobolev s hs0)) hn

#print axioms FullModeMorseBott.localMaximum_sobolev
end BecknerOnofri.HighDim
