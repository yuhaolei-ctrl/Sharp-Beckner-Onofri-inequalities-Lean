import BecknerOnofri.EndpointRigidity.Reduction
import BecknerOnofri.EndpointFromTwelve

/-! Equality propagates down the actual marginal energy/entropy chain. The
only dimension-specific rigidity input is the twelve-dimensional mixture base. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.EndpointRigidity
open Legacy.TorusEndpoint Legacy.BecknerOnofri CosineMixtureTransfer

/-- Rigidity in the exact countable-mixture notation of the endpoint induction. -/
def MixtureRigidity (d : ℕ) : Prop :=
  ∀ (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ),
    (∀ n, 0 ≤ w n) → HasSum w 1 →
    Summable (fun n => w n * CosineMixture.tensor (N n) 0) →
    (∀ x, 0 < CosineMixtureApproximation.rho w N x) →
    energy (d:ℝ) (CosineMixtureApproximation.rho w N) =
      2 * densityEntropy (CosineMixtureApproximation.rho w N) →
    ∀ x, CosineMixtureApproximation.rho w N x = 1

theorem mixture_rigidity_successor {d : ℕ} (hd : 12 ≤ d)
    (hEndpoint : MixtureEndpoint d) (hRigidity : MixtureRigidity d) :
    MixtureRigidity (d+1) := by
  intro w N hw hm hSup hpos he
  let f := CosineMixtureApproximation.rho w N
  let q : Fin (d+1) → Torus d → ℝ := fun i =>
    CosineMixtureApproximation.rho w (fun n => drop i (N n))
  let Q : Fin (d+1) → ℝ := fun i => energy (d:ℝ) (q i)
  let E : Fin (d+1) → ℝ := fun i => densityEntropy (q i)
  have hd0 : (0:ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hDim : energy ((d+1:ℕ):ℝ) f ≤ (1/(d:ℝ)) * ∑ i, Q i :=
    countable_mixture_dimension_transfer hd w N hw hm.summable hSup
  have hEnt : (∑ i, E i) ≤ (d:ℝ) * densityEntropy f :=
    mixture_entropy_deletion_le w N hw hm hSup hpos
  have hMarg (i : Fin (d+1)) : Q i ≤ 2 * E i :=
    hEndpoint w (fun n => drop i (N n)) hw hm
      (summable_drop_majorant i w N hw hSup) (rho_drop_pos i w N hw hSup hpos)
  have hLower : (d:ℝ) * energy ((d+1:ℕ):ℝ) f ≤ ∑ i, Q i := by
    have h := mul_le_mul_of_nonneg_left hDim hd0.le
    calc
      _ ≤ (d:ℝ) * ((1/(d:ℝ)) * ∑ i, Q i) := h
      _ = _ := by field_simp
  have hGapNonneg (i : Fin (d+1)) : 0 ≤ 2 * E i - Q i := sub_nonneg.mpr (hMarg i)
  have hGapSum : (∑ i, (2 * E i - Q i)) = 0 := by
    apply le_antisymm
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      change energy ((d+1:ℕ):ℝ) f = 2 * densityEntropy f at he
      nlinarith
    · exact Finset.sum_nonneg (fun i _ => hGapNonneg i)
  have hEqual (i : Fin (d+1)) : Q i = 2 * E i := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hGapNonneg i)).mp hGapSum i
      (Finset.mem_univ i)
    linarith
  have hUniform (i : Fin (d+1)) : ∀ x, q i x = 1 :=
    hRigidity w (fun n => drop i (N n)) hw hm
      (summable_drop_majorant i w N hw hSup) (rho_drop_pos i w N hw hSup hpos) (hEqual i)
  have hEzero (i : Fin (d+1)) : E i = 0 := by
    simp only [E, densityEntropy, hUniform i, Real.log_one, mul_zero, integral_zero]
  have hQzero (i : Fin (d+1)) : Q i = 0 := by rw [hEqual, hEzero, mul_zero]
  have hEntNonpos : densityEntropy f ≤ 0 := by
    simp only [hQzero, Finset.sum_const_zero, mul_zero] at hDim
    change energy ((d+1:ℕ):ℝ) f = 2 * densityEntropy f at he
    linarith
  let r := CosineMixtureApproximation.probabilityDensity w N hw hm hSup
  have hr : r.FiniteEntropy := CosineMixtureApproximation.rho_finiteEntropy w N hw hm hSup
  have hZero : densityEntropy r.value = 0 :=
    le_antisymm hEntNonpos (densityEntropy_nonneg_of_finite r hr)
  have hae := (EntropyVariationalEquality.entropy_eq_zero_iff r hr).mp hZero
  haveI : (torusMeasure (d+1)).IsOpenPosMeasure := by
    rw [torusMeasure_explicit]
    infer_instance
  exact congrFun (Measure.eq_of_ae_eq hae
    (CosineMixtureApproximation.rho_continuous w N hw hSup) continuous_const)

theorem mixture_rigidity_from_twelve (h12 : MixtureEndpoint 12)
    (hRig12 : MixtureRigidity 12) {d : ℕ} (hd : 12 ≤ d) : MixtureRigidity d := by
  induction d, hd using Nat.le_induction with
  | base => exact hRig12
  | succ d hd ih =>
    exact mixture_rigidity_successor hd (mixture_endpoint_from_twelve h12 hd) ih

/-- Match the mixture series predicate with the genuine probability-density
predicate used by the full finite-entropy rigidity reduction. -/
theorem positiveMixtureRigidity_of_mixtureRigidity {d : ℕ} (hd : 0 < d)
    (hRigidity : MixtureRigidity d) : PositiveMixtureRigidity d (1/2) := by
  intro r _hc hp hMix he
  obtain ⟨w, N, hw, hm, hSup, heq⟩ := hMix
  have hpos : ∀ x, 0 < CosineMixtureApproximation.rho w N x := by rwa [← heq]
  have henergy : energy (d:ℝ) (CosineMixtureApproximation.rho w N) =
      2 * densityEntropy (CosineMixtureApproximation.rho w N) := by
    rw [← heq, energy_eq_legacy hd]
    linarith
  rw [heq]
  exact hRigidity w N hw hm hSup hpos henergy

/-- Full finite-entropy rigidity in the base dimension supplies precisely the
pointwise mixture rigidity required by the induction. -/
theorem mixtureRigidity_of_densityRigidity {d : ℕ} (hd : 0 < d)
    (hRigid : ∀ r : ProbabilityDensity d, r.FiniteEntropy →
      (1/2:ℝ) * fourierEnergy r = densityEntropy r.value →
      r.value =ᵐ[torusMeasure d] (fun _ => 1)) : MixtureRigidity d := by
  intro w N hw hm hSup _hp he
  let r := CosineMixtureApproximation.probabilityDensity w N hw hm hSup
  have hr : r.FiniteEntropy := CosineMixtureApproximation.rho_finiteEntropy w N hw hm hSup
  have heq : (1/2:ℝ) * fourierEnergy r = densityEntropy r.value := by
    change energy (d:ℝ) r.value = 2 * densityEntropy r.value at he
    rw [energy_eq_legacy hd] at he
    linarith
  have hae := hRigid r hr heq
  haveI : (torusMeasure d).IsOpenPosMeasure := by
    rw [torusMeasure_explicit]
    infer_instance
  exact congrFun (Measure.eq_of_ae_eq hae
    (CosineMixtureApproximation.rho_continuous w N hw hSup) continuous_const)

/-- Full finite-entropy equality rigidity in every d≥12 follows from the two
precise d=12 mixture inputs, inequality and equality rigidity. -/
theorem uniform_from_twelve (h12 : MixtureEndpoint 12) (hRig12 : MixtureRigidity 12)
    {d : ℕ} (hd : 12 ≤ d) (r : ProbabilityDensity d) (hr : r.FiniteEntropy)
    (he : (1/2:ℝ) * fourierEnergy r = densityEntropy r.value) :
    r.value =ᵐ[torusMeasure d] (fun _ => 1) :=
  uniform_of_equality (by omega) (by norm_num)
    (finite_entropy_endpoint_from_mixture hd (mixture_endpoint_from_twelve h12 hd))
    (positiveMixtureRigidity_of_mixtureRigidity (by omega)
      (mixture_rigidity_from_twelve h12 hRig12 hd)) r hr he

#print axioms mixture_rigidity_successor
#print axioms uniform_from_twelve
end BecknerOnofri.EndpointRigidity
