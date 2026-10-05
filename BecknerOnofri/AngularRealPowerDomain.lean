import BecknerOnofri.AngularRealPowerIntertwining

/-! Domain and closed graph of the positive real spectral power, and
preservation of rapid Fourier summability by positive real powers.
The Friedrichs quadratic-form identification is a separate obligation. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BecknerOnofri.AngularRealPower
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev RadialWiener AngularMixedTerms AngularMixedL2
open JacobiTensor JacobiTensorSpectrum AngularSpectralIntertwining

lemma powerGraph_iff_repr {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    (u v : TensorL2 d) :
    PowerGraph α hα s hs u v ↔ ∀ n,
      (hilbertBasis α).repr v n=(tensorEigenvalue α n)^s*(hilbertBasis α).repr u n := by
  constructor
  · intro h n; exact powerGraph_repr α hα s hs h n
  · intro h
    apply (hilbertBasis α).repr.injective
    ext n
    have hp : 0 < tensorEigenvalue α n := (positiveSpectrum α hα).value_pos n
    rw [repr_inversePower,h n,← mul_assoc,← Real.rpow_add hp]
    simp

/-- The unbounded power has exactly its usual weighted square-summable domain. -/
theorem powerGraph_domain {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    (u : TensorL2 d) :
    (∃ v,PowerGraph α hα s hs u v) ↔
      Memℓp (fun n => (tensorEigenvalue α n)^s*(hilbertBasis α).repr u n) 2 := by
  constructor
  · rintro ⟨v,hv⟩
    have he : (fun n => (tensorEigenvalue α n)^s*(hilbertBasis α).repr u n)=
        (hilbertBasis α).repr v := funext (fun n => (powerGraph_repr α hα s hs hv n).symm)
    rw [he]; exact lp.memℓp _
  · intro h
    refine ⟨(hilbertBasis α).repr.symm ⟨_,h⟩,?_⟩
    apply (powerGraph_iff_repr α hα s hs _ _).mpr
    intro n
    exact congrArg (fun x : lp (fun _ : Index d => ℝ) 2 => x n)
      ((hilbertBasis α).repr.apply_symm_apply _)

theorem powerGraph_closed {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s) :
    IsClosed {p : TensorL2 d × TensorL2 d | PowerGraph α hα s hs p.1 p.2} :=
  isClosed_eq ((inversePower α hα s hs).continuous.comp continuous_snd) continuous_fst

theorem powerGraph_limit {d : ℕ} {ι : Type*} (l : Filter ι) [NeBot l]
    (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    (u v : ι → TensorL2 d) (u₀ v₀ : TensorL2 d)
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀))
    (h : ∀ᶠ j in l,PowerGraph α hα s hs (u j) (v j)) :
    PowerGraph α hα s hs u₀ v₀ := by
  apply tendsto_nhds_unique_of_eventuallyEq
    (((inversePower α hα s hs).continuous.tendsto v₀).comp hv) hu
  exact h

lemma radial_power_bound {d : ℕ} (t : ℝ) (ht : 0≤t) (N : ℕ) (hN : t≤N)
    (k : Frequency d) : frequencyRadius k^t≤radialWeight N k := by
  calc
    _ ≤ (1+frequencyRadius k)^t := Real.rpow_le_rpow (frequencyRadius_nonneg k)
      (by linarith) ht
    _ ≤ (1+frequencyRadius k)^(N:ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by linarith [frequencyRadius_nonneg k]) hN
    _ = _ := by rw [Real.rpow_natCast]; rfl

/-- A positive real Fourier multiplier preserves every polynomial Wiener norm. -/
theorem real_power_radialSummable {d : ℕ} (t : ℝ) (ht : 0≤t)
    (a : Frequency d → ℂ) (ha : ∀ m : ℕ,RadialSummable a m) (m : ℕ) :
    RadialSummable (fun k => ((frequencyRadius k^t:ℝ):ℂ)*a k) m := by
  obtain ⟨N,hN⟩ := exists_nat_ge t
  apply (ha (m+N)).of_nonneg_of_le
    (fun k => mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))
  intro k
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg
    (frequencyRadius_nonneg k) t)]
  calc
    _ ≤ radialWeight m k*(radialWeight N k*‖a k‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (radial_power_bound t ht N hN k) (norm_nonneg _))
        ((radialWeight_isWeight m).nonneg k)
    _ = radialWeight (m+N) k*‖a k‖ := by simp only [radialWeight,pow_add]; ring

/-- The all-s intertwining needs rapid decay only for the input, because
rapid decay of its positive-power image is a theorem. -/
theorem positive_intertwining_of_rapid {d : ℕ} (s : ℝ) (hs : 0<s)
    (a : Frequency d → ℂ) (ha : ∀ m : ℕ,RadialSummable a m)
    (is : List (Fin d)) (his : is≠[]) :
    PowerGraph (countIndex is) (countIndex_ne_zero is his) s hs
      (vector a is) (vector (fun k => ((frequencyRadius k^(2*s):ℝ):ℂ)*a k) is) :=
  positive_intertwining s hs a _
    (real_power_radialSummable (2*s) (by positivity) a ha) (fun _ _ => rfl) is his

#print axioms powerGraph_domain
#print axioms powerGraph_closed
#print axioms powerGraph_limit
#print axioms positive_intertwining_of_rapid

end BecknerOnofri.AngularRealPower
