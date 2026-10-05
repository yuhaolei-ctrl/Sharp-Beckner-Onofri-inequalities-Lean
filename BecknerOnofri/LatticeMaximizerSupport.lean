module

public import BecknerOnofri.CosineCoefficientLattice
public import BecknerOnofri.PositiveFourierSupport

@[expose] public section

/-! Genuine Euler support groups for all nonnegative coefficient maximizers,
including the actual maximum and minimum candidates from supermodularity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate
namespace BecknerOnofri.HighDim.CosineCoefficientLattice
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler
open PositiveFourierSupport

private theorem rough {d : ℕ} (hd : 0<d) :
    RoughExponentialBound d (endpointConstant d/2)
      (GreenRoughEnergy.partition d (endpointConstant d/2)) := by
  have hC : 0<endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  exact GenericAttainment.rough_bound hd (by positivity) (by linarith)

theorem toPotential_fourier_summable {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) :
    Summable (fun k => ‖fourierIsometry d (toPotential a) k‖) := by
  simpa only [toPotential_coefficient ha,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (ha.nonneg _)] using ha.summable

theorem toPotential_density_exponential {d : ℕ} {a : Frequency d → ℝ} (ha : Domain a) (k : Frequency d) :
    densityFourier (gibbsValue (toPotential a)) k=(fourierExponential a k : ℂ)/(partition (toPotential a) : ℂ) := by
  have h := WienerFourier.normalized_real_exp_coefficient (toPotential a)
    (toPotential_fourier_summable ha) (toPotential_admissible ha).1 (partition (toPotential a)) k
  change densityFourier (gibbsValue (toPotential a)) k=_ at h
  rw [show (fourierIsometry d (toPotential a) : Frequency d → ℂ)=(fun j => (a j : ℂ)) from
    funext (toPotential_coefficient ha),exponentialCoefficients_ofReal] at h
  exact h

theorem toPotential_support_euler {d : ℕ} (hd : 0<d) {a : Frequency d → ℝ} (ha : Domain a)
    {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a))
    (k : Frequency d) (hk : k≠0) (hp : 0<fourierExponential a k) : 0<a k := by
  have h := congrArg Complex.re (maximizer_fourier_formula (rough hd) hA (toPotential_admissible ha) hmax hk)
  rw [toPotential_coefficient ha,toPotential_density_exponential ha] at h
  simp only [← Complex.ofReal_div,← Complex.ofReal_mul,Complex.ofReal_re] at h
  rw [h]
  exact mul_pos (mul_pos (div_pos zero_lt_one (mul_pos (by norm_num) hA))
    (inv_pos.mpr (pow_pos (frequencyRadius_pos hk) _)))
    (div_pos hp (SubcriticalAttainment.partition_pos (rough hd) (toPotential_admissible ha)))

def maximizerSupport {d : ℕ} (hd : 0<d) {a : Frequency d → ℝ} (ha : Domain a)
    {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a)) :
    AddSubgroup (Frequency d) :=
  supportGroup a ha.nonneg ha.summable ha.even (toPotential_support_euler hd ha hA hmax)

@[simp] theorem mem_maximizerSupport {d : ℕ} (hd : 0<d) {a : Frequency d → ℝ} (ha : Domain a)
    {A : ℝ} (hA : 0<A)
    (hmax : ∀ v : TorusL2 d,Admissible v → functional A v≤functional A (toPotential a)) (k : Frequency d) :
    k∈maximizerSupport hd ha hA hmax ↔ k=0 ∨ 0<a k := Iff.rfl

/-- A union of two additive subgroups can be a subgroup only when one
contains the other. The proof is constructive from closure under subtraction. -/
theorem subgroup_union_comparable {G : Type*} [AddCommGroup G] (L M N : AddSubgroup G)
    (hN : ∀ x,x∈N ↔ x∈L ∨ x∈M) : L≤M ∨ M≤L := by
  by_cases hLM : L≤M
  · exact Or.inl hLM
  · right
    obtain ⟨x,hxL,hxM⟩ : ∃ x,x∈L ∧ x∉M := by
      by_contra h
      apply hLM
      intro x hx
      by_contra hnot
      exact h ⟨x,hx,hnot⟩
    intro y hyM
    have hxy : x+y∈N := N.add_mem ((hN x).mpr (Or.inl hxL)) ((hN y).mpr (Or.inr hyM))
    rcases (hN (x+y)).mp hxy with hL | hM
    · simpa only [add_sub_cancel_left] using L.sub_mem hL hxL
    · have hx : x∈M := by simpa only [add_sub_cancel_right] using M.sub_mem hM hyM
      exact False.elim (hxM hx)

#print axioms maximizerSupport
#print axioms subgroup_union_comparable
end BecknerOnofri.HighDim.CosineCoefficientLattice
