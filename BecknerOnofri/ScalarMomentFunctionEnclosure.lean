module

public import BecknerOnofri.ScalarCheckedBessel

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open CircleScalar Set

/-- Monotonicity of the actual Bessel moments turns endpoint enclosures into
an enclosure on every point of the parameter interval. -/
theorem moment_interval (n : ℕ) (l u : CheckedMoment)
    (hl : l.order=n) (hu : u.order=n) (hpos : 0≤l.argument)
    {x : ℝ} (hx : x∈Icc (l.argument : ℝ) (u.argument : ℝ)) :
    (l.value.lower : ℝ)≤besselMoment n x ∧ besselMoment n x≤(u.value.upper : ℝ) := by
  have hl0 : (0 : ℝ)≤l.argument := by exact_mod_cast hpos
  have hx0 := hl0.trans hx.1
  have hu0 := hx0.trans hx.2
  have hlo := l.sound.1
  have hup := u.sound.2
  rw [hl] at hlo
  rw [hu] at hup
  exact ⟨hlo.trans (besselMoment_mono n hl0 hx0 hx.1),
    (besselMoment_mono n hx0 hu0 hx.2).trans hup⟩

def momentDerivativeInterval (prev next current first : RationalInterval) : RationalInterval :=
  (prev.add next).add (((⟨2,2⟩ : RationalInterval).mul (current.mul first)).neg)

theorem momentDerivativeInterval_sound (n : ℕ) (x : ℝ)
    (prev next current first : RationalInterval)
    (hp : prev.Contains (besselMoment (n-1) x))
    (hn : next.Contains (besselMoment (n+1) x))
    (hc : current.Contains (besselMoment n x))
    (hf : first.Contains (besselMoment 1 x)) :
    (momentDerivativeInterval prev next current first).Contains
      (besselMoment (n-1) x+besselMoment (n+1) x-2*besselMoment n x*besselMoment 1 x) := by
  have h2 : (⟨2,2⟩ : RationalInterval).Contains (2 : ℝ) := by
    norm_num [RationalInterval.Contains]
  have h := RationalInterval.contains_add (RationalInterval.contains_add hp hn)
    (RationalInterval.contains_neg (RationalInterval.contains_mul h2
      (RationalInterval.contains_mul hc hf)))
  simpa only [sub_eq_add_neg,mul_assoc,momentDerivativeInterval] using h

noncomputable def momentFunctionEnclosure (a b : ℝ) (n : ℕ) (hn : 1≤n)
    (prev next current first : RationalInterval)
    (hp : ∀ x∈Icc a b,prev.Contains (besselMoment (n-1) x))
    (hq : ∀ x∈Icc a b,next.Contains (besselMoment (n+1) x))
    (hc : ∀ x∈Icc a b,current.Contains (besselMoment n x))
    (hf : ∀ x∈Icc a b,first.Contains (besselMoment 1 x)) :
    FunctionEnclosure a b (besselMoment n) where
  value := current
  slope := momentDerivativeInterval prev next current first
  value_mem := hc
  slope_bounds := by
    apply slopeBounds_of_hasDerivAt
      (fun x _ => (besselMoment_derivative n hn x).continuousAt.continuousWithinAt)
      (fun x _ => besselMoment_derivative n hn x)
    intro x hx
    have hmem := Ioo_subset_Icc_self hx
    exact momentDerivativeInterval_sound n x prev next current first
      (hp x hmem) (hq x hmem) (hc x hmem) (hf x hmem)

#print axioms momentFunctionEnclosure
end BecknerOnofri.HighDim.ScalarCertificate
