module

public import Legacy.BecknerOnofri.AngularPartialSigns
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-! Transfer of actual L2 angular signs back to the entire closed unit cube,
including the boundary, using continuity and the full-support product measure. -/
noncomputable section
namespace Legacy.BecknerOnofri.AngularCubeOrder
open Set MeasureTheory Legacy.TorusEndpoint TorusSobolev RadialWiener AngularMixedTerms AngularMixedL2

def openBox (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Ioo 0 Real.pi)
def closedBox (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Icc 0 Real.pi)

theorem openBox_isOpen (d : ℕ) : IsOpen (openBox d) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem closure_openBox (d : ℕ) : closure (openBox d) = closedBox d := by
  rw [openBox, closure_pi_set]
  simp only [closure_Ioo Real.pi_pos.ne]
  rfl

theorem measure_restrict (d : ℕ) : JacobiTensor.measure d =
    (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict (openBox d) := by
  rw [openBox, Measure.restrict_pi_pi]
  rfl

theorem angularCube_continuous (d : ℕ) : Continuous (@angularCube d) := by
  apply continuous_pi
  intro i
  exact (continuous_const.add (Real.continuous_cos.comp (continuous_apply i))).div_const 2

def inverseCube {d : ℕ} (y : Fin d → ℝ) : Fin d → ℝ := fun i => Real.arccos (2*y i-1)

theorem inverseCube_mem {d : ℕ} (y : Fin d → ℝ) : inverseCube y ∈ closedBox d := by
  intro i _
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

theorem angularCube_inverse {d : ℕ} {y : Fin d → ℝ} (hy : y ∈ FiniteDifferences.closedCube d) :
    angularCube (inverseCube y) = y := by
  funext i
  have hi := ChebyshevProfile.mem_closedCube.mp (CubeProfileMonotone.fromUnitCube_mapsTo d hy) i
  change 2*y i-1 ∈ Icc (-1 : ℝ) 1 at hi
  change (1+Real.cos (Real.arccos (2*y i-1)))/2 = y i
  rw [Real.cos_arccos hi.1 hi.2]
  ring

theorem nonnegative_of_angular_ae {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hg : ContinuousOn g (FiniteDifferences.closedCube d))
    (hpos : ∀ᵐ x ∂JacobiTensor.measure d, 0 ≤ g (angularCube x)) :
    ∀ y ∈ FiniteDifferences.closedCube d, 0 ≤ g y := by
  have hc : Continuous (fun x => g (angularCube x)) :=
    hg.comp_continuous (angularCube_continuous d) (angularCube_mem)
  have he : (fun x => min (g (angularCube x)) 0) =ᵐ[JacobiTensor.measure d] (fun _ => (0 : ℝ)) := by
    filter_upwards [hpos] with x hx
    exact min_eq_right hx
  rw [measure_restrict] at he
  have hpoint := Measure.eqOn_open_of_ae_eq he (openBox_isOpen d)
    (hc.min continuous_const).continuousOn continuousOn_const
  have hclosed : IsClosed {x : Fin d → ℝ | 0 ≤ g (angularCube x)} :=
    isClosed_le continuous_const hc
  have hsubset : openBox d ⊆ {x : Fin d → ℝ | 0 ≤ g (angularCube x)} := by
    intro x hx
    have he := hpoint hx
    exact (min_eq_right_iff.mp he)
  have hcl := closure_minimal hsubset hclosed
  rw [closure_openBox] at hcl
  intro y hy
  have h := hcl (inverseCube_mem y)
  change 0 ≤ g (angularCube (inverseCube y)) at h
  rwa [angularCube_inverse hy] at h

theorem eq_zero_of_angular_ae {d : ℕ} {g : (Fin d → ℝ) → ℝ}
    (hg : ContinuousOn g (FiniteDifferences.closedCube d))
    (hz : ∀ᵐ x ∂JacobiTensor.measure d, g (angularCube x) = 0) :
    ∀ y ∈ FiniteDifferences.closedCube d, g y = 0 := by
  have hp := nonnegative_of_angular_ae hg (hz.mono (fun _ h => h.ge))
  have hn := nonnegative_of_angular_ae hg.neg (hz.mono (fun _ h => by change 0 ≤ -_; rw [h]; simp))
  intro y hy
  exact le_antisymm (neg_nonneg.mp (hn y hy)) (hp y hy)

theorem mixedPartial_nonnegative_of_vector {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d))
    (hv : PositiveOperatorNeumann.Nonnegative (JacobiTensor.measure d) (vector a is)) :
    ∀ y ∈ FiniteDifferences.closedCube d, 0 ≤ FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y := by
  apply nonnegative_of_angular_ae
    (FiniteDifferences.contDiffOn_mixedPartial
      (CubeProfileMonotone.unit_profile_contDiffOn (ChebyshevProfile.profile_contDiffOn a ha)) is).continuousOn
  filter_upwards [hv, vector_ae a ha is, JacobiTensor.ae_mem_box d] with x hp he hx
  rw [he] at hp
  exact (mul_nonneg_iff_of_pos_left (AngularPartialSigns.weight_pos is hx)).mp hp

theorem mixedPartial_zero_of_vector {d : ℕ} (a : Frequency d → ℂ)
    (ha : ∀ m : ℕ, RadialSummable a m) (is : List (Fin d)) (hv : vector a is = 0) :
    ∀ y ∈ FiniteDifferences.closedCube d, FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) y = 0 := by
  apply eq_zero_of_angular_ae
    (FiniteDifferences.contDiffOn_mixedPartial
      (CubeProfileMonotone.unit_profile_contDiffOn (ChebyshevProfile.profile_contDiffOn a ha)) is).continuousOn
  have he := vector_ae a ha is
  rw [hv] at he
  filter_upwards [he, Lp.coeFn_zero ℝ 2 (JacobiTensor.measure d), JacobiTensor.ae_mem_box d] with x hx hz hb
  have h : weight is x * FiniteDifferences.mixedPartial is
      (fun z => ChebyshevProfile.profile a (CubeProfileMonotone.fromUnitCube z)) (angularCube x) = 0 := by
    rw [← hx, hz]
    rfl
  exact (mul_eq_zero.mp h).resolve_left (AngularPartialSigns.weight_pos is hb).ne'

#print axioms mixedPartial_nonnegative_of_vector
#print axioms mixedPartial_zero_of_vector
end Legacy.BecknerOnofri.AngularCubeOrder
