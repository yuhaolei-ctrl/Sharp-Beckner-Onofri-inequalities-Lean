module

public import BecknerOnofri.SelectedMarginalCorrelation
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Parseval consequences of the actual selected-maximizer symmetries. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000
open MeasureTheory Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open GinibreCovariance ContinuousGibbs CosineCoefficientLattice

theorem densityMode_parseval {u : TorusL2 12} (hu : Selected u) :
    HasSum (fun k => densityMode u k^2) (densityNorm u^2) := by
  have h := RawComplementGap.raw_fourier_square_hasSum (gibbsValue u) (gibbsValue_memLp_two rough hu.1)
  have hn : ∫ x,(gibbsValue u x)^2 ∂torusMeasure 12=densityNorm u^2 := by
    rw [densityNorm,Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg _))]
  rw [hn] at h
  apply h.congr_fun
  intro k
  symm
  change ‖densityFourier (gibbsValue u) k‖^2=_
  rw [densityFourier_eq_mode hu]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem densityMode_finite_parseval {u : TorusL2 12} (hu : Selected u)
    (S : Finset (Frequency 12)) : (∑ k∈S,densityMode u k^2)≤densityNorm u^2 :=
  sum_le_hasSum S (fun k _ => sq_nonneg _) (densityMode_parseval hu)

/-- Genuine signed coordinate orbit, with duplicates removed. -/
def signedOrbit {d : ℕ} (k : Frequency d) : Finset (Frequency d) := by
  classical
  exact Finset.univ.image (fun p : (Fin d → Bool)×Equiv.Perm (Fin d) =>
    fun i => if p.1 i then -k (p.2 i) else k (p.2 i))

theorem mem_signedOrbit_self {d : ℕ} (k : Frequency d) : k∈signedOrbit k := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(fun _ => false,Equiv.refl _),Finset.mem_univ _,rfl⟩

theorem mem_signedOrbit_iff {d : ℕ} (k l : Frequency d) :
    l∈signedOrbit k ↔ ∃ (ε : Fin d → Bool) (σ : Equiv.Perm (Fin d)),
      l=(fun i => if ε i then -k (σ i) else k (σ i)) := by
  classical
  simp only [signedOrbit,Finset.mem_image,Finset.mem_univ,true_and,Prod.exists]
  constructor
  · rintro ⟨ε,σ,h⟩; exact ⟨ε,σ,h.symm⟩
  · rintro ⟨ε,σ,h⟩; exact ⟨ε,σ,h.symm⟩

attribute [irreducible] signedOrbit

theorem densityMode_signedOrbit {u : TorusL2 12} (hu : Selected u)
    {k l : Frequency 12} (hl : l∈signedOrbit k) : densityMode u l=densityMode u k := by
  classical
  obtain ⟨ε,σ,rfl⟩ := (mem_signedOrbit_iff k l).mp hl
  calc
    _ = densityMode u (ContinuousSymmetry.frequencyPermutation σ.symm k) := by
      apply densityMode_same_abs hu
      intro i
      simp only [ContinuousSymmetry.frequencyPermutation,Equiv.symm_symm]
      split_ifs <;> simp
    _ = _ := densityMode_permutation hu σ.symm k

/-- The exact orbit-cardinality Parseval estimate, before taking square roots. -/
theorem densityMode_orbit_square {u : TorusL2 12} (hu : Selected u) (k : Frequency 12) :
    (signedOrbit k).card*(densityMode u k)^2≤densityNorm u^2 := by
  have h := densityMode_finite_parseval hu (signedOrbit k)
  have he : (∑ l∈signedOrbit k,densityMode u l^2)=(signedOrbit k).card*densityMode u k^2 := by
    calc
      _ = ∑ _l∈signedOrbit k,densityMode u k^2 := Finset.sum_congr rfl (fun l hl => by rw [densityMode_signedOrbit hu hl])
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  rwa [he] at h

/-- Source orbit cap for any certified upper bound on the actual Gibbs L² norm. -/
theorem densityMode_orbit_cap {u : TorusL2 12} (hu : Selected u) (k : Frequency 12)
    {M : ℝ} (hM : densityNorm u≤M) :
    densityMode u k≤M/Real.sqrt (signedOrbit k).card := by
  have hcard : (0:ℝ)<(signedOrbit k).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨k,mem_signedOrbit_self k⟩
  have hn : 0≤densityNorm u := Real.sqrt_nonneg _
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hcard)).mpr
  have hs := densityMode_orbit_square hu k
  have hsq : (densityMode u k*Real.sqrt (signedOrbit k).card)^2≤M^2 := by
    rw [mul_pow,Real.sq_sqrt hcard.le]
    nlinarith [sq_nonneg (M-densityNorm u)]
  nlinarith [mul_nonneg (densityMode_nonneg hu k) (Real.sqrt_nonneg ((signedOrbit k).card : ℝ))]

theorem densityMode_axis_eq {u : TorusL2 12} (hu : Selected u)
    (i j : Fin 12) (n : ℤ) : densityMode u (Pi.single i n)=densityMode u (Pi.single j n) := by
  classical
  have he : ContinuousSymmetry.frequencyPermutation (Equiv.swap i j) (Pi.single i n)=Pi.single j n := by
    ext a
    simp only [ContinuousSymmetry.frequencyPermutation,Equiv.swap_inv,Pi.single_apply]
    by_cases hi : a=i <;> by_cases hj : a=j <;> by_cases hij : i=j <;> simp_all [Equiv.swap_apply_def,eq_comm]
  rw [← he,densityMode_permutation hu]

/-- The common axis modes, already identified across all twelve marginals. -/
def axisMode (u : TorusL2 12) (n : ℤ) : ℝ := densityMode u (Pi.single (0 : Fin 12) n)

theorem densityMode_axis {u : TorusL2 12} (hu : Selected u) (i : Fin 12) (n : ℤ) :
    densityMode u (Pi.single i n)=axisMode u n := densityMode_axis_eq hu i 0 n

theorem axisMode_square_summable {u : TorusL2 12} (hu : Selected u) :
    Summable (fun n => axisMode u n^2) := by
  apply (densityMode_parseval hu).summable.comp_injective
  intro a b he
  have h := congrFun he (0 : Fin 12)
  simpa using h

/-- Finite-box form of the product Parseval argument. -/
theorem axisMode_finite_power_bound {u : TorusL2 12} (hu : Selected u) (S : Finset ℤ) :
    (∑ n∈S,axisMode u n^2)^12≤densityNorm u^2 := by
  classical
  rw [Finset.sum_pow']
  apply (Finset.sum_le_sum (fun k _ => ?_)).trans
    (densityMode_finite_parseval hu (Fintype.piFinset (fun _ : Fin 12 => S)))
  have h := densityMode_coordinate_product hu k
  simp_rw [densityMode_axis hu] at h
  rw [Finset.prod_pow]
  exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => densityMode_nonneg hu _)) h 2

/-- The common one-dimensional Fourier square sum obeys the exact twelfth
power bound. A later Fubini lemma identifies this sum with the marginal L² norm. -/
theorem axisMode_power_bound {u : TorusL2 12} (hu : Selected u) :
    (∑' n,axisMode u n^2)^12≤densityNorm u^2 := by
  exact le_of_tendsto ((axisMode_square_summable hu).hasSum.pow 12)
    (Eventually.of_forall (axisMode_finite_power_bound hu))

#print axioms densityMode_orbit_cap
#print axioms axisMode_power_bound
end BecknerOnofri.HighDim.SelectedNumericalModel
