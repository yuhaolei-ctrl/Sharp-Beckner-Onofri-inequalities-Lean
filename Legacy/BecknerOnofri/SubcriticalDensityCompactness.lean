module

public import Legacy.BecknerOnofri.GibbsL2Continuity
public import Legacy.BecknerOnofri.SubcriticalDensityEuler

@[expose] public section

/-! The set of all actual L2 density maximizers is compact in L2.  This
supports selection by maximizing a continuous moment on the optimizer set. -/
noncomputable section
namespace Legacy.BecknerOnofri.SubcriticalDensityCompactness
open Set MeasureTheory Legacy.TorusEndpoint TorusSobolev SubcriticalAttainment SubcriticalEuler
open SubcriticalPrimalDual GibbsL2Continuity

def coerciveRadius (b Ab A : ℝ) : ℝ := (Real.log Ab+1)/(A-1/(4*b))

theorem coerciveRadius_nonneg {d : ℕ} {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 1/(4*b) < A) :
    0 ≤ coerciveRadius b Ab A :=
  div_nonneg (by linarith [rough_log_nonneg hR]) (sub_pos.mpr hA).le

theorem maximizer_mem_ball {d : ℕ} {b Ab A : ℝ}
    (hR : RoughExponentialBound d b Ab) (hA : 1/(4*b) < A)
    {u : TorusL2 d} (hu : Admissible u)
    (hmax : ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u) :
    u ∈ realSobolevBall d (coerciveRadius b Ab A) := by
  have hz : 0 ≤ functional A u := by simpa using hmax 0 (admissible_zero d)
  have hc := coercivity hR A hu
  refine ⟨⟨hu.2, ?_⟩, hu.1⟩
  apply (le_div_iff₀ (sub_pos.mpr hA)).mpr
  nlinarith

def maximizingPotentials (d : ℕ) (A B : ℝ) : Set (EnergyBall d B) :=
  {u | ∀ v : TorusL2 d, Admissible v → functional A v ≤ functional A u.1}

theorem maximizingPotentials_isClosed {d : ℕ} {b Ab A B : ℝ} (hb : 0 < b)
    (hA : 0 ≤ A) (hR : RoughExponentialBound d b Ab) :
    IsClosed (maximizingPotentials d A B) := by
  have hsc : UpperSemicontinuous (fun u : EnergyBall d B => functional A u.1) :=
    (lowerSemicontinuous_restrict_iff (f := fun u : TorusL2 d => OrderDual.toDual (functional A u))).mpr
      (functional_upperSemicontinuousOn_ball hb hA hR)
  have he : maximizingPotentials d A B =
      ⋂ v : TorusL2 d, ⋂ _ : Admissible v, {u : EnergyBall d B | functional A v ≤ functional A u.1} := by
    ext u
    simp [maximizingPotentials]
  rw [he]
  exact isClosed_iInter (fun v => isClosed_iInter (fun _ => hsc.isClosed_preimage (functional A v)))

def densityMaximizers (d : ℕ) (A : ℝ) : Set (DensityL2 d) :=
  {r | ∃ q : ProbabilityDensity d, ∃ hq : MemLp q.value 2 (torusMeasure d),
    r = hq.toLp q.value ∧
    ∀ s : ProbabilityDensity d, MemLp s.value 2 (torusMeasure d) → densityFunctional A s ≤ densityFunctional A q}

theorem densityMaximizers_eq_image {d : ℕ} (hd : 0 < d) {b Ab A : ℝ} (hb : 0 < b)
    (hA : 1/(4*b) < A) (hR : RoughExponentialBound d b Ab) :
    densityMaximizers d A =
      (gibbsLp hR) '' maximizingPotentials d A (coerciveRadius b Ab A) := by
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*b)).trans hA
  ext r
  constructor
  · rintro ⟨q, hq, rfl, hmax⟩
    have hv := dualPotential_admissible hd A q hq
    have hvmax := (density_maximizer_dual hd hR hA0 q hq hmax).2
    let v : EnergyBall d (coerciveRadius b Ab A) :=
      ⟨dualPotential A q hq, maximizer_mem_ball hR hA hv hvmax⟩
    refine ⟨v, hvmax, ?_⟩
    apply Lp.ext
    filter_upwards [gibbsLp_ae hR v, hq.coeFn_toLp,
      density_maximizer_gibbs hd hR hA0 q hq hmax] with x hx hy hz
    exact hx.trans (hz.symm.trans hy.symm)
  · rintro ⟨u, hu, rfl⟩
    let q := gibbsDensity hR (ball_admissible u)
    have hq : MemLp q.value 2 (torusMeasure d) := gibbsValue_memLp_two hR (ball_admissible u)
    refine ⟨q, hq, ?_, gibbs_density_maximizer hd hR hA0 (ball_admissible u) hu⟩
    apply Lp.ext
    filter_upwards [gibbsLp_ae hR u, hq.coeFn_toLp] with x hx hy
    exact hx.trans hy.symm

theorem densityMaximizers_isCompact_of_rough {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hb : 0 < b) (hA : 1/(4*b) < A) (hR : RoughExponentialBound d b Ab) :
    IsCompact (densityMaximizers d A) := by
  have hA0 : 0 ≤ A := ((by positivity : 0 < 1/(4*b)).trans hA).le
  letI : CompactSpace (EnergyBall d (coerciveRadius b Ab A)) :=
    isCompact_iff_compactSpace.mp (realSobolevBall_isCompact hd (coerciveRadius_nonneg hR hA))
  rw [densityMaximizers_eq_image hd hb hA hR]
  exact (maximizingPotentials_isClosed hb hA0 hR).isCompact.image (gibbsLp_continuous hb hR)

theorem densityMaximizers_nonempty_of_rough {d : ℕ} (hd : 0 < d) {b Ab A : ℝ}
    (hb : 0 < b) (hA : 1/(4*b) < A) (hR : RoughExponentialBound d b Ab) :
    (densityMaximizers d A).Nonempty := by
  obtain ⟨u, hu, hE, _, hmax⟩ := exists_global_maximizer hd hb hA hR
  rw [densityMaximizers_eq_image hd hb hA hR]
  exact ⟨gibbsLp hR ⟨u, ⟨⟨hu.2, hE⟩, hu.1⟩⟩, ⟨⟨u, ⟨⟨hu.2, hE⟩, hu.1⟩⟩, hmax, rfl⟩⟩

theorem exists_rough_below_subcritical {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) :
    ∃ b Ab : ℝ, 0 < b ∧ 1/(4*b) < A ∧ RoughExponentialBound d b Ab := by
  have hC : 0 < endpointConstant d := div_pos (Nat.cast_pos.mpr hd) (endpointSigma_pos hd)
  have hA0 : 0 < A := (by positivity : 0 < 1/(4*endpointConstant d)).trans hA
  have hbC : 1/(4*A) < endpointConstant d := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 4*endpointConstant d)).mp hA
    apply (div_lt_iff₀ (by positivity : 0 < 4*A)).mpr
    nlinarith
  obtain ⟨b, hb, hbd⟩ := exists_between hbC
  have hb0 : 0 < b := (by positivity : 0 < 1/(4*A)).trans hb
  have hAb : 1/(4*b) < A := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 4*A)).mp hb
    apply (div_lt_iff₀ (by positivity : 0 < 4*b)).mpr
    nlinarith
  exact ⟨b, GreenRoughEnergy.partition d b, hb0, hAb, roughExponentialBound hd hb0 hbd⟩

/-- Unconditional compactness and nonemptiness for every subcritical coefficient. -/
theorem densityMaximizers_compact_nonempty {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) :
    IsCompact (densityMaximizers d A) ∧ (densityMaximizers d A).Nonempty := by
  obtain ⟨b, Ab, hb, hAb, hR⟩ := exists_rough_below_subcritical hd hA
  exact ⟨densityMaximizers_isCompact_of_rough hd hb hAb hR,
    densityMaximizers_nonempty_of_rough hd hb hAb hR⟩

theorem exists_maximal_moment {d : ℕ} (hd : 0 < d) {A : ℝ}
    (hA : 1/(4*endpointConstant d) < A) (L : DensityL2 d → ℝ) (hL : Continuous L) :
    ∃ r ∈ densityMaximizers d A, ∀ q ∈ densityMaximizers d A, L q ≤ L r := by
  obtain ⟨hc, hn⟩ := densityMaximizers_compact_nonempty hd hA
  exact hc.exists_isMaxOn hn hL.continuousOn

#print axioms densityMaximizers_compact_nonempty
#print axioms exists_maximal_moment
end Legacy.BecknerOnofri.SubcriticalDensityCompactness
