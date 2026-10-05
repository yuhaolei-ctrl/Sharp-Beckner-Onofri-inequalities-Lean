import Legacy.BecknerOnofri.EndpointOnofri

/-! Exact transfer of density endpoint rigidity to the potential equality
classification. Density rigidity is kept explicit, since it is false in the
circle case; no equality classification is inferred from Endpoint alone. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.EndpointPotential
open TorusSobolev SubcriticalAttainment SubcriticalEuler SobolevCentering

/-- The density-side equality classification, separate from validity of the inequality. -/
def DensityEqualityRigidity (d : ℕ) : Prop :=
  ∀ r : ProbabilityDensity d, r.FiniteEntropy →
    endpointConstant d*fourierEnergy r = densityEntropy r.value →
      r.value =ᵐ[torusMeasure d] fun _ => 1

/-- The L2 equality class already suffices for potential rigidity, because the
Gibbs density of every admissible potential belongs to L2. -/
def L2DensityEqualityRigidity (d : ℕ) : Prop :=
  ∀ r : ProbabilityDensity d, MemLp r.value 2 (torusMeasure d) →
    endpointConstant d*fourierEnergy r = densityEntropy r.value →
      r.value =ᵐ[torusMeasure d] fun _ => 1

theorem zero_of_gibbs_uniform {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    {u : TorusL2 d} (hu : Admissible u) (hg : gibbsValue u =ᵐ[torusMeasure d] fun _ => 1) : u = 0 := by
  have he : u =ᵐ[torusMeasure d] fun _ => ((Real.log (partition u) : ℝ) : ℂ) := by
    filter_upwards [hg,hu.1] with x hx hi
    have hl := log_gibbsValue (rough_of_endpoint hd hE) hu x
    rw [hx,Real.log_one] at hl
    apply Complex.ext
    · change (u x).re = Real.log (partition u)
      linarith
    · exact hi
  have huconst : u = constant d (Real.log (partition u) : ℂ) :=
    Lp.ext (he.trans (constant_ae d _).symm)
  have hzero := hu.2.1
  rw [huconst,constant_fourier] at hzero
  simp only [ite_true] at hzero
  rw [huconst,hzero]
  exact map_zero (Lp.const 2 (torusMeasure d))

theorem equality_iff_zero_of_L2 {d : ℕ} (hd : 0 < d) (hE : Endpoint d) (hRigid : L2DensityEqualityRigidity d)
    {u : TorusL2 d} (hu : Admissible u) :
    Real.log (partition u) = coefficient d*criticalEnergy u ↔ u = 0 := by
  constructor
  · intro he
    apply zero_of_gibbs_uniform hd hE hu
    exact hRigid (gibbsDensity (rough_of_endpoint hd hE) hu)
      (gibbsValue_memLp_two (rough_of_endpoint hd hE) hu)
      (gibbs_equality_of_potential_equality hd hE hu he)
  · rintro rfl
    simp

theorem equality_iff_zero {d : ℕ} (hd : 0 < d) (hE : Endpoint d) (hRigid : DensityEqualityRigidity d)
    {u : TorusL2 d} (hu : Admissible u) :
    Real.log (partition u) = coefficient d*criticalEnergy u ↔ u = 0 := by
  constructor
  · intro he
    apply zero_of_gibbs_uniform hd hE hu
    exact hRigid (gibbsDensity (rough_of_endpoint hd hE) hu)
      (gibbsDensity_finiteEntropy (rough_of_endpoint hd hE) hu)
      (gibbs_equality_of_potential_equality hd hE hu he)
  · rintro rfl
    simp

theorem centered_equality_iff_constant {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    (hRigid : DensityEqualityRigidity d) {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Real.log (centeredPartition u) = coefficient d*criticalEnergy u ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c : ℂ) := by
  rw [centeredPartition_eq,← center_energy hd u,
    equality_iff_zero hd hE hRigid (center_admissible hd hr hs),center_zero_iff_constant]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c.re,?_⟩
    filter_upwards [hc,hr] with x hx hi
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using congrArg Complex.re hx
    · simpa only [Complex.ofReal_im] using hi
  · rintro ⟨c,hc⟩
    exact ⟨(c : ℂ),hc⟩

theorem manuscript_equality_iff_constant {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    (hRigid : DensityEqualityRigidity d) {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Real.log (centeredPartition u) = (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c : ℂ) := by
  rw [← coefficient_manuscript hd u hs]
  exact centered_equality_iff_constant hd hE hRigid hr hs

theorem centered_equality_iff_constant_of_L2 {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    (hRigid : L2DensityEqualityRigidity d) {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Real.log (centeredPartition u) = coefficient d*criticalEnergy u ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c : ℂ) := by
  rw [centeredPartition_eq,← center_energy hd u,
    equality_iff_zero_of_L2 hd hE hRigid (center_admissible hd hr hs),center_zero_iff_constant]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c.re,?_⟩
    filter_upwards [hc,hr] with x hx hi
    apply Complex.ext
    · simpa only [Complex.ofReal_re] using congrArg Complex.re hx
    · simpa only [Complex.ofReal_im] using hi
  · rintro ⟨c,hc⟩
    exact ⟨(c : ℂ),hc⟩

theorem manuscript_equality_iff_constant_of_L2 {d : ℕ} (hd : 0 < d) (hE : Endpoint d)
    (hRigid : L2DensityEqualityRigidity d) {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) :
    Real.log (centeredPartition u) = (1/(4*(d:ℝ)*endpointSymbolConstant d))*manuscriptEnergy u ↔
      ∃ c : ℝ, u =ᵐ[torusMeasure d] fun _ => (c : ℂ) := by
  rw [← coefficient_manuscript hd u hs]
  exact centered_equality_iff_constant_of_L2 hd hE hRigid hr hs

#print axioms equality_iff_zero_of_L2
#print axioms equality_iff_zero
#print axioms manuscript_equality_iff_constant
end Legacy.BecknerOnofri.EndpointPotential
