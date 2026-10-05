import PhysicalForm
import BecknerOnofri.Friedrichs.MixedSpectralPowers

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped BigOperators
namespace BecknerOnofri.Paper2.Physical
open Friedrichs.MixedSpatial

/-- Conjugacy of the actual closed-form operator graphs, including their domains. -/
theorem operatorGraph_transport {d : ℕ} (α : MultiIndex d)
    (f g : Friedrichs.MixedSpatial.H α) :
    operatorGraph α (coordinateLpEquiv α f) (scale^2 • coordinateLpEquiv α g) ↔
      Friedrichs.MixedSpatial.operatorGraph α f g := by
  constructor
  · rintro ⟨v,hvf,hvc,hv⟩
    obtain ⟨v',hv'c,rfl⟩ := (show v ∈ energyEquiv α '' Friedrichs.MixedSpatial.formClosure α by
      rw [energyEquiv_closure_image]; exact hvc)
    have hv'f : v'.1=f := (coordinateLpEquiv α).injective hvf
    refine ⟨v',hv'f,hv'c,fun w hw => ?_⟩
    have hh := congrArg (fun t : ℝ => scale^d*t)
      (hv (energyEquiv α w) ((energyEquiv_mem_closure α w).mpr hw))
    rw [energyEquiv_pairing] at hh
    change scale^2 * Friedrichs.MixedSpatial.formPairing v' w =
      scale^d * inner ℝ (scale^2 • coordinateLpEquiv α g) (coordinateLpEquiv α w.1) at hh
    simp only [inner_smul_left,conj_trivial] at hh
    have hi := coordinateLpEquiv_inner α g w.1
    apply (mul_left_cancel₀ (pow_ne_zero 2 scale_ne))
    linear_combination hh + scale^2 * hi
  · rintro ⟨v,hvf,hvc,hv⟩
    refine ⟨energyEquiv α v, congrArg (coordinateLpEquiv α) hvf,
      (energyEquiv_mem_closure α v).mpr hvc, ?_⟩
    intro w hw
    obtain ⟨w',hw'c,rfl⟩ := (show w ∈ energyEquiv α '' Friedrichs.MixedSpatial.formClosure α by
      rw [energyEquiv_closure_image]; exact hw)
    apply (mul_left_cancel₀ (pow_ne_zero d scale_ne))
    rw [energyEquiv_pairing,hv w' hw'c]
    change scale^2 * inner ℝ g w'.1 =
      scale^d * inner ℝ (scale^2 • coordinateLpEquiv α g) (coordinateLpEquiv α w'.1)
    simp only [inner_smul_left,conj_trivial]
    have hi := coordinateLpEquiv_inner α g w'.1
    linear_combination -scale^2 * hi

/-- Physical spectral powers on the actual unit-period mixed L² space.
The transported complete mixed basis retains the periodic odd modes. -/
def SpectralPowerGraph {d : ℕ} (α : MultiIndex d) (s : ℝ) (f g : H α) : Prop :=
  ∀ n, inner ℝ g (coordinateLpEquiv α (basisTensorVector α n)) =
    (scale^2 * mixedEigenvalue α n)^s *
      inner ℝ f (coordinateLpEquiv α (basisTensorVector α n))

lemma powerScale_pos (s : ℝ) : 0 < (scale^2)^s := Real.rpow_pos_of_pos (sq_pos_of_ne_zero scale_ne) _

theorem spectralPowerGraph_transport {d : ℕ} (α : MultiIndex d) (s : ℝ)
    (f g : Friedrichs.MixedSpatial.H α) :
    SpectralPowerGraph α s (coordinateLpEquiv α f)
      ((scale^2)^s • coordinateLpEquiv α g) ↔
      Friedrichs.MixedSpatial.SpectralPowerGraph α s f g := by
  have he (n : MultiIndex d) : (scale^2 * mixedEigenvalue α n)^s =
      (scale^2)^s * (mixedEigenvalue α n)^s :=
    Real.mul_rpow (sq_nonneg _) (by unfold mixedEigenvalue; positivity)
  constructor
  · intro h n
    have hn := congrArg (fun t : ℝ => scale^d*t) (h n)
    rw [he] at hn
    simp only [inner_smul_left,conj_trivial] at hn
    have hf := coordinateLpEquiv_inner α f (basisTensorVector α n)
    have hg := coordinateLpEquiv_inner α g (basisTensorVector α n)
    apply (mul_left_cancel₀ (powerScale_pos s).ne')
    linear_combination hn - (scale^2)^s * hg + ((scale^2)^s * (mixedEigenvalue α n)^s) * hf
  · intro h n
    rw [he]
    simp only [inner_smul_left,conj_trivial]
    apply (mul_left_cancel₀ (pow_ne_zero d scale_ne))
    have hf := coordinateLpEquiv_inner α f (basisTensorVector α n)
    have hg := coordinateLpEquiv_inner α g (basisTensorVector α n)
    have hn := h n
    linear_combination (scale^2)^s * hg - ((scale^2)^s * (mixedEigenvalue α n)^s) * hf + (scale^2)^s * hn

theorem spectralPowerGraph_one {d : ℕ} (α : MultiIndex d) (f g : H α) :
    SpectralPowerGraph α 1 f g ↔ operatorGraph α f g := by
  let f' := (coordinateLpEquiv α).symm f
  let g' := (scale^2)⁻¹ • (coordinateLpEquiv α).symm g
  have hf : coordinateLpEquiv α f'=f := (coordinateLpEquiv α).apply_symm_apply f
  have hg : scale^2 • coordinateLpEquiv α g'=g := by simp [g',map_smul,smul_smul,scale_ne]
  rw [← hf,← hg,← Real.rpow_one (scale^2)]
  rw [spectralPowerGraph_transport, Real.rpow_one, operatorGraph_transport,
    Friedrichs.MixedSpatial.spectralPowerGraph_one]

/-- Domain equality under physical change of coordinates, for every real power. -/
theorem spectralPowerGraph_domain {d : ℕ} (α : MultiIndex d) (s : ℝ)
    (f : Friedrichs.MixedSpatial.H α) :
    (∃ g : H α, SpectralPowerGraph α s (coordinateLpEquiv α f) g) ↔
      ∃ g : Friedrichs.MixedSpatial.H α, Friedrichs.MixedSpatial.SpectralPowerGraph α s f g := by
  constructor
  · rintro ⟨g,hg⟩
    let g' := ((scale^2)^s)⁻¹ • (coordinateLpEquiv α).symm g
    have he : (scale^2)^s • coordinateLpEquiv α g'=g := by
      simp [g',map_smul,smul_smul,(powerScale_pos s).ne']
    exact ⟨g',(spectralPowerGraph_transport α s f g').mp (he.symm ▸ hg)⟩
  · rintro ⟨g,hg⟩
    exact ⟨_,(spectralPowerGraph_transport α s f g).mpr hg⟩

#print axioms operatorGraph_transport
#print axioms spectralPowerGraph_one
#print axioms spectralPowerGraph_domain
end BecknerOnofri.Paper2.Physical
