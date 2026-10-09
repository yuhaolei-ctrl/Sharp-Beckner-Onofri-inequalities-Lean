module

public import BecknerOnofri.V2.FiniteState.FamilyLocal
public import BecknerOnofri.V2.FiniteState.OriginOrthogonality
public import BecknerOnofri.SpinDifferentialDefinitions

@[expose] public section

/-!
# Origin expansions of the spin moments, the interaction term and the gradient

Appendix A.3: with `M_s(t) = ∑_j A_{s,j} p_j(t)` one has `M_1 = t + O(t³)`, `M_2 = (32/31) t² + O(t³)`,
`M_s = O(t³)` for `s ≥ 3`; hence `(Wp)_j = 12 x_j t + (66/31) A_{2,j} t² + O(t³)` and
`g_j(p(t)) = 2 - 12 t² + O(t³)`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState
open BecknerOnofri.HighDim.Spin

/-- `M_s(p) = ∑_j A_{s,j} p_j`. -/
def famMomentOf (s : Order) (p : Count → ℝ) : ℝ := ∑ j : Count, moment s j * p j

/-- `M_s(t) = ∑_j A_{s,j} p_j(t)`. -/
def famMoment (s : Order) (t : ℝ) : ℝ := ∑ j : Count, moment s j * famLaw t j

theorem famEll_eq (j : Count) : famEll j = 12 * moment ⟨0, by decide⟩ j := by
  rw [moment_one, meanCoordinate_eq_real]; unfold famEll; ring

theorem famD2_eq (j : Count) : famD2 j = (32 / 31) * (66 * moment ⟨1, by decide⟩ j) := by
  rw [moment_two, meanCoordinate_eq_real]; unfold famD2; ring

theorem famMoment_jet (s : Order) :
    Jet2 (famMoment s) 0 (if s.val = 0 then 1 else 0) (if s.val = 1 then 32 / 31 else 0) := by
  have hj : ∀ j ∈ (Finset.univ : Finset Count),
      Jet2 (fun t => (reference j * moment s j) * (famLaw t j / reference j))
        ((reference j * moment s j) * 1) ((reference j * moment s j) * famEll j)
        ((reference j * moment s j) * famD2 j) :=
    fun j _ => (famLaw_ratio_jet j).const_mul _
  have H := Jet2.sum Finset.univ hj
  have e : ∀ t, famMoment s t =
      ∑ j : Count, (reference j * moment s j) * (famLaw t j / reference j) := by
    intro t
    unfold famMoment
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := (reference_pos j).ne'
    field_simp
  refine (H.congr e).coeff ?_ ?_ ?_
  · -- value
    have := reference_moment_zero s
    simp only [mul_one]
    rw [← this]
  · -- linear coefficient
    have h := reference_moment_orthogonal s ⟨0, by decide⟩
    have e2 : ∑ j : Count, (reference j * moment s j) * famEll j =
        12 * ∑ j : Count, reference j * (moment s j * moment ⟨0, by decide⟩ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [famEll_eq]; ring
    rw [e2, h]
    by_cases hs : s.val = 0
    · have : s = ⟨0, by decide⟩ := Fin.ext hs
      subst this
      simp [Nat.choose]
    · have : s ≠ ⟨0, by decide⟩ := fun h' => hs (by rw [h'])
      simp only [this, hs, ↓reduceIte, mul_zero]
  · -- quadratic coefficient
    have h := reference_moment_orthogonal s ⟨1, by decide⟩
    have e2 : ∑ j : Count, (reference j * moment s j) * famD2 j =
        (32 / 31 * 66) * ∑ j : Count, reference j * (moment s j * moment ⟨1, by decide⟩ j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [famD2_eq]; ring
    rw [e2, h]
    by_cases hs : s.val = 1
    · have : s = ⟨1, by decide⟩ := Fin.ext hs
      subst this
      norm_num [Nat.choose]
    · have : s ≠ ⟨1, by decide⟩ := fun h' => hs (by rw [h'])
      simp only [this, hs, ↓reduceIte, mul_zero]

theorem weight_zero : weight ⟨0, by decide⟩ = 12 := by
  unfold weight weightQ
  norm_num [Nat.choose]

theorem weight_one : weight ⟨1, by decide⟩ = 33 / 16 := by
  unfold weight weightQ
  norm_num [Nat.choose]

theorem sum_order_ite (f : Order → ℝ) (n : ℕ) (hn : n < 12) (c : ℝ) :
    ∑ s : Order, f s * (if s.val = n then c else 0) = f ⟨n, hn⟩ * c := by
  rw [Finset.sum_eq_single_of_mem (⟨n, hn⟩ : Order) (Finset.mem_univ _)]
  · simp
  · intro s _ hs
    have : s.val ≠ n := fun h => hs (Fin.ext h)
    simp [this]

theorem interaction_sum_eq (p : Count → ℝ) (j : Count) :
    ∑ k : Count, interaction j k * p k =
      ∑ s : Order, weight s * moment s j * famMomentOf s p := by
  simp only [interaction_eq, famMomentOf, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem famWp_jet (j : Count) :
    Jet2 (fun t => ∑ k : Count, interaction j k * famLaw t k) 0 (famEll j)
      ((2 * ((j.val : ℝ) - 6) ^ 2 - 6) / 31) := by
  have hs : ∀ s ∈ (Finset.univ : Finset Order),
      Jet2 (fun t => weight s * moment s j * famMomentOf s (famLaw t)) (weight s * moment s j * 0)
        (weight s * moment s j * (if s.val = 0 then 1 else 0))
        (weight s * moment s j * (if s.val = 1 then 32 / 31 else 0)) :=
    fun s _ => (famMoment_jet s).const_mul _
  have H := Jet2.sum Finset.univ hs
  refine (H.congr (fun t => ?_)).coeff ?_ ?_ ?_
  · simp_rw [interaction_sum_eq]
  · simp
  · rw [sum_order_ite (fun s => weight s * moment s j) 0 (by norm_num) 1, weight_zero, famEll_eq]
    ring
  · rw [sum_order_ite (fun s => weight s * moment s j) 1 (by norm_num) (32 / 31), weight_one,
      moment_two, meanCoordinate_eq_real]
    ring

/-- `g_j(p(t)) = 2 - 12 t² + O(t³)` (`d12-spin-eq:eorigin`). -/
theorem famGrad_jet (j : Count) : Jet2 (fun t => gradient (famLaw t) j) 2 0 (-12) := by
  have hl := (famLaw_ratio_jet j).log_one
  have h1 := ((hl.const_mul 2).add (Jet2.const 2)).sub ((famWp_jet j).const_mul 2)
  refine (h1.congr (fun t => ?_)).coeff (by ring) (by ring) ?_
  · unfold gradient; ring
  · unfold famD2 famEll; ring

theorem famGradResidual_isBigO (j : Count) :
    (fun t => gradient (famLaw t) j - (2 - 12 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  have h := famGrad_jet j
  unfold Jet2 at h
  refine h.congr_left (fun t => ?_)
  ring

end BecknerOnofri.V2.FiniteState
