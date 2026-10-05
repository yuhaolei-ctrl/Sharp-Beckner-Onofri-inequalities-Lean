module

public import BecknerOnofri.RadialThetaTail
public import Legacy.BecknerOnofri.CircleHeatPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section

/-! Actual spatial-theta radial geometry and monotonicity. The stronger
off-diagonal comparison is not assumed here: it requires a separate proof
identifying the normalized Jacobi product with the actual theta series. -/
noncomputable section
open Set
open scoped BigOperators
namespace BecknerOnofri.HighDim.SpatialThetaDiagonal
open RadialThetaTail

def radialAngle (d : ℕ) (S : ℝ) : ℝ := Real.arcsin (Real.sqrt (S/(d:ℝ)))/Real.pi

def radialTheta (d : ℕ) (t S : ℝ) : ℝ := theta t (radialAngle d S)^d

def sineSquareSum {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, Real.sin (Real.pi*x i)^2

theorem sineSquareSum_mem {d : ℕ} (x : Fin d → ℝ) :
    sineSquareSum x∈Icc (0:ℝ) d := by
  constructor
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · calc
      _ ≤ ∑ _i : Fin d, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi*x i),sq_nonneg (Real.cos (Real.pi*x i))]
      _ = _ := by simp

theorem ratio_mem {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Icc (0:ℝ) d) :
    S/(d:ℝ)∈Icc (0:ℝ) 1 := by
  have hp : (0:ℝ)<d := Nat.cast_pos.mpr hd
  exact ⟨div_nonneg hS.1 hp.le,(div_le_one hp).mpr hS.2⟩

theorem radialAngle_mem {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Icc (0:ℝ) d) :
    radialAngle d S∈Icc (0:ℝ) (1/2) := by
  refine ⟨div_nonneg (Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)) Real.pi_pos.le,?_⟩
  apply (div_le_iff₀ Real.pi_pos).mpr
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using Real.arcsin_le_pi_div_two (Real.sqrt (S/(d:ℝ)))

theorem radialAngle_monotone (d : ℕ) : Monotone (radialAngle d) := by
  intro S T hST
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  exact Real.arcsin_le_arcsin (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hST (Nat.cast_nonneg d)))

/-- The inverse sine coordinate has exactly the required averaged squared sine. -/
theorem sineSquare_radialAngle {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Icc (0:ℝ) d) :
    Real.sin (Real.pi*radialAngle d S)^2=S/(d:ℝ) := by
  have hs := ratio_mem hd hS
  have hroot : Real.sqrt (S/(d:ℝ))≤1 := by
    exact (Real.sqrt_le_one).mpr hs.2
  unfold radialAngle
  rw [mul_div_cancel₀ _ Real.pi_pos.ne',Real.sin_arcsin
    (by linarith [Real.sqrt_nonneg (S/(d:ℝ))]) hroot,Real.sq_sqrt hs.1]

theorem theta_pos {t : ℝ} (ht : 0<t) (y : ℝ) : 0<theta t y :=
  Legacy.TorusEndpoint.TorusHeatPositivity.theta_re_pos (div_pos ht Real.pi_pos) _

theorem theta_antitone {t : ℝ} (ht : 0<t) :
    AntitoneOn (theta t) (Icc (0:ℝ) (1/2)) :=
  Legacy.BecknerOnofri.CircleHeat.realHeat_antitone (div_pos ht Real.pi_pos)

/-- Antitonicity of the actual diagonal spatial theta profile, proved from
the actual periodized Gaussian rather than a presumed product formula. -/
theorem radialTheta_antitone {d : ℕ} (hd : 0<d) {t : ℝ} (ht : 0<t) :
    AntitoneOn (radialTheta d t) (Icc (0:ℝ) d) := by
  intro S hS T hT hST
  exact pow_le_pow_left₀ (theta_pos ht _).le
    (theta_antitone ht (radialAngle_mem hd hS) (radialAngle_mem hd hT)
      (radialAngle_monotone d hST)) d

theorem radialTheta_pos {d : ℕ} {t : ℝ} (ht : 0<t) (S : ℝ) :
    0<radialTheta d t S := pow_pos (theta_pos ht _) d

theorem sineSquareSum_diagonal {d : ℕ} (hd : 0<d) {S : ℝ} (hS : S∈Icc (0:ℝ) d) :
    sineSquareSum (fun _ : Fin d => radialAngle d S)=S := by
  unfold sineSquareSum
  simp only [sineSquare_radialAngle hd hS,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ S (by exact_mod_cast hd.ne')

#print axioms radialTheta_antitone
#print axioms sineSquare_radialAngle
end BecknerOnofri.HighDim.SpatialThetaDiagonal
