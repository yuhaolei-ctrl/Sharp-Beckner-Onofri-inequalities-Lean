module

public import BecknerOnofri.V2.Reaudit.MorseBott.OrbitMap
public import BecknerOnofri.V2.Reaudit.MorseBott.TranslateInvariance
public import BecknerOnofri.V2.Reaudit.MorseBott.Tangent
public import BecknerOnofri.V2.Reaudit.MorseBott.CriticalSet
public import BecknerOnofri.LocalElevenCore.SupportedFullIdentification

@[expose] public section

/-! # The embedded critical manifold of the full-support branch

Separate geometric statement (`prop:section5-local-branches`, Morse--Bott assertion made exact):
for the full-support branch `u = branch univ δ` at small `δ > 0`,

* `x₀ ↦ u(· + x₀)`, `𝕋^d → H^s`, is a smooth immersion (injective differential) and a
  topological (closed) embedding, with smooth local slice charts;
* the critical points in the `H^s` tube around the orbit are exactly the orbit;
* the Hessian kernel `{h : d²Φ(u)[h,h] = 0}` is exactly the tangent space of the orbit.

This is a new theorem; `FullModeMorseBott` is untouched. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven

section Slice
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

/-- The cube of phases around `t₀`. -/
def phaseCube (t₀ : Fin d → ℝ) : Set (Fin d → ℝ) := {t | ∀ j, |t j - t₀ j| < 1 / 2}

theorem isOpen_phaseCube (t₀ : Fin d → ℝ) : IsOpen (phaseCube t₀) := by
  have : phaseCube t₀ = ⋂ j : Fin d, (fun t : Fin d → ℝ => t j) ⁻¹' Metric.ball (t₀ j) (1 / 2) := by
    ext t; simp [phaseCube, Real.dist_eq]
  rw [this]
  exact isOpen_iInter_of_finite (fun j => Metric.isOpen_ball.preimage (continuous_apply j))

theorem isOpenMap_lift : IsOpenMap (lift : (Fin d → ℝ) → Torus d) := by
  have : (lift : (Fin d → ℝ) → Torus d) =
      Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle)) := rfl
  rw [this]
  exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall (fun _ => QuotientAddGroup.mk_surjective))

/-- **Slice charts**: near each orbit point there is an open `U ⊂ H^s` with `U ∩ orbit` equal to the
image of a phase cube, and a smooth retraction onto the phases defined on `U`. -/
theorem exists_slice_chart (hd : 0 < d) (hall : ∀ σ : ℝ, 0 ≤ σ → InSobolev σ u)
    (hs : 0 ≤ s) (hu : InSobolev s u)
    (hfull : ∀ j : Fin d, fourierCoeff u (axisFrequency j) ≠ 0) (t₀ : Fin d → ℝ) :
    ∃ U : Set (FourierL2 d), IsOpen U ∧
      U ∩ Set.range (orbitMapT hu) = orbitMap hu '' phaseCube t₀ ∧
      ContDiffOn ℝ ∞ (phaseCoord hu t₀) U ∧
      ∀ t ∈ phaseCube t₀, phaseCoord hu t₀ (orbitMap hu t) = t := by
  obtain ⟨hopen, -, hsm, hkey⟩ := exists_smooth_left_inverse hu hfull t₀
  have hemb := (isClosedEmbedding_orbitMapT hd hall hs hu hfull).isEmbedding
  have hW : IsOpen (lift '' phaseCube t₀ : Set (Torus d)) :=
    isOpenMap_lift _ (isOpen_phaseCube t₀)
  obtain ⟨V, hV, hVW⟩ := hemb.isInducing.isOpen_iff.mp hW
  refine ⟨V ∩ phaseDomain hu t₀, hV.inter hopen, ?_, hsm.mono Set.inter_subset_right, ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨hyV, -⟩, x, rfl⟩
      have hx : x ∈ orbitMapT hu ⁻¹' V := hyV
      rw [hVW] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨?_, (hkey t ht).1⟩, lift t, rfl⟩
      have : lift t ∈ orbitMapT hu ⁻¹' V := by
        rw [hVW]; exact ⟨t, ht, rfl⟩
      exact this
  · intro t ht
    exact (hkey t ht).2

end Slice

section Tube
variable {d : ℕ} {s : ℝ}

/-- Rigidity of critical points in an `H^s`-ball around `u`. -/
def CriticalBallRigidity (μ s ρ : ℝ) (u : Torus d → ℝ) : Prop :=
  ∀ v : Torus d → ℝ, InSobolev s v → MeanZero v → IsCritical μ v →
    InSobolev s (fun x => v x - u x) → sobolevNorm s (fun x => v x - u x) < ρ →
    ∃ a : Torus d, v =ᵐ[torusMeasure d] translate u a

/-- Ball rigidity at `u` propagates to the whole tube around the orbit, by translation invariance. -/
theorem tube_of_ball {μ ρ : ℝ} {u : Torus d → ℝ} (h : CriticalBallRigidity μ s ρ u) :
    ∀ (v : Torus d → ℝ) (a₀ : Torus d), InSobolev s v → MeanZero v → IsCritical μ v →
      InSobolev s (fun x => v x - translate u a₀ x) →
      sobolevNorm s (fun x => v x - translate u a₀ x) < ρ →
      ∃ a : Torus d, v =ᵐ[torusMeasure d] translate u a := by
  intro v a₀ hSv hmv hcv hSd hn
  have hfun : (fun x => translate v (-a₀) x - u x) =
      translate (fun x => v x - translate u a₀ x) (-a₀) := by
    funext x
    simp only [translate]
    have : x - -a₀ - a₀ = x := by abel
    simp
  have hS' : InSobolev s (fun x => translate v (-a₀) x - u x) := by
    rw [hfun]; exact (inSobolev_translate_iff s _ _).mpr hSd
  have hn' : sobolevNorm s (fun x => translate v (-a₀) x - u x) < ρ := by
    rw [hfun, sobolevNorm_translate]; exact hn
  obtain ⟨a, ha⟩ := h (translate v (-a₀)) ((inSobolev_translate_iff s v _).mpr hSv)
    ((meanZero_translate_iff v _).mpr hmv) ((isCritical_translate_iff _).mpr hcv) hS' hn'
  refine ⟨a + a₀, ?_⟩
  have h1 := (ae_eq_translate_iff _ _ a₀).mpr ha
  rw [translate_neg_translate, translate_translate] at h1
  exact h1

end Tube

section Main
variable {d : ℕ} {s : ℝ} {u : Torus d → ℝ}

/-- **Embedded critical orbit** (exact geometric form of the Morse--Bott assertion for the full
branch).  Here `β` is the coupling, `μ = β / β_s(d)`, `u` the potential, and `hu : u ∈ H^s`. -/
structure EmbeddedCriticalOrbit (β s : ℝ) (u : Torus d → ℝ) (hu : InSobolev s u) : Prop where
  /-- the orbit map `t ↦ u(· - t)`, `ℝ^d → H^s`, is `C^∞` -/
  contDiff : ContDiff ℝ ∞ (orbitMap hu)
  /-- it is an immersion -/
  immersion : ∀ t, Function.Injective (fderiv ℝ (orbitMap hu) t)
  /-- the torus orbit map is a closed topological embedding -/
  embedding : Topology.IsClosedEmbedding (orbitMapT hu)
  /-- smooth slice charts: the image is a `d`-dimensional embedded submanifold of `H^s` -/
  sliceChart : ∀ t₀ : Fin d → ℝ, ∃ U : Set (FourierL2 d), IsOpen U ∧
    U ∩ Set.range (orbitMapT hu) = orbitMap hu '' phaseCube t₀ ∧
    ContDiffOn ℝ ∞ (phaseCoord hu t₀) U ∧
    ∀ t ∈ phaseCube t₀, phaseCoord hu t₀ (orbitMap hu t) = t
  /-- every orbit point is a critical point of the dual functional -/
  orbitCritical : ∀ a : Torus d, InSobolev s (translate u a) ∧ MeanZero (translate u a) ∧
    IsCritical (β / spectralThreshold d) (translate u a)
  /-- the critical points in an `H^s`-tube around the orbit are exactly (a.e.) orbit points -/
  criticalSet : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (v : Torus d → ℝ) (a₀ : Torus d),
    InSobolev s v → MeanZero v → IsCritical (β / spectralThreshold d) v →
    InSobolev s (fun x => v x - translate u a₀ x) →
    sobolevNorm s (fun x => v x - translate u a₀ x) < ρ →
    ∃ a : Torus d, v =ᵐ[torusMeasure d] translate u a
  /-- Hessian kernel = tangent space of the orbit, at every orbit point -/
  hessianKernel_eq_tangent : ∀ (t : Fin d → ℝ) (h : Torus d → ℝ), InCriticalSobolev h → MeanZero h →
    (secondVariation β (translate u (lift t)) h = 0 ↔
      ∃ hS : InSobolev s h, encodeSobolev h hS ∈ Set.range (fderiv ℝ (orbitMap hu) t))

/-- Assembly: the embedded-orbit structure follows from `FullModeMorseBott` plus ball rigidity. -/
theorem embeddedCriticalOrbit_of_fullMode (hd : 0 < d) {β ρ : ℝ} (hρ : 0 < ρ)
    (hu : FullModeMorseBott β u) (hs : 0 ≤ s)
    (hball : CriticalBallRigidity (β / spectralThreshold d) s ρ u) :
    EmbeddedCriticalOrbit β s u (hu.sobolev s hs) where
  contDiff := orbitMap_contDiff hd hu.sobolev hs (hu.sobolev s hs)
  immersion := fderiv_orbitMap_injective hd hu.sobolev hs (hu.sobolev s hs) hu.fullModes
  embedding := isClosedEmbedding_orbitMapT hd hu.sobolev hs (hu.sobolev s hs) hu.fullModes
  sliceChart := exists_slice_chart hd hu.sobolev hs (hu.sobolev s hs) hu.fullModes
  orbitCritical := fun a => ⟨(inSobolev_translate_iff s u a).mpr (hu.sobolev s hs),
    (meanZero_translate_iff u a).mpr hu.meanZero,
    isCritical_translate (isCritical_of_stationary hu.stationary) a⟩
  criticalSet := ⟨ρ, hρ, tube_of_ball hball⟩
  hessianKernel_eq_tangent := by
    intro t h hc hm
    have hT := fullModeMorseBott_translate hu (lift t)
    rw [hT.hessianKernel h hc hm]
    exact tangent_iff_range_fderiv hd hu.sobolev hs (hu.sobolev s hs) hu.smooth t h

end Main

section Branch
variable {d : ℕ}

/-- **Embedded Morse--Bott critical manifold of the full-support branch, from the existing
`FullModeMorseBott` family.**  The hypothesis `hmb` is the existing theorem
`SupportedFamily.full_branch_morse_bott` (kept as a hypothesis here so that this module does not
import the legacy local-maximality chain; it is discharged in `FullBranch.lean`). -/
theorem full_branch_embedded_orbit_of_morse_bott (hd : 11 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 < s)
    (hmb : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      FullModeMorseBott ((1 / (1 - δ)) * spectralThreshold d)
        (SupportedFamily.branch hd Finset.univ δ)) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∃ hu : InSobolev s (SupportedFamily.branch hd Finset.univ δ),
        EmbeddedCriticalOrbit ((1 / (1 - δ)) * spectralThreshold d) s
          (SupportedFamily.branch hd Finset.univ δ) hu := by
  have hd0 : 0 < d := by omega
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hσ : 0 < spectralThreshold d := Legacy.TorusEndpoint.endpointSigma_pos (by omega)
  filter_upwards [hmb, exists_ball_critical hd hs] with δ hmb ⟨ρ, hρ, hball⟩
  refine ⟨hmb.sobolev s hs0, ?_⟩
  refine embeddedCriticalOrbit_of_fullMode hd0 hρ hmb hs0 ?_
  have : (1 / (1 - δ)) * spectralThreshold d / spectralThreshold d = 1 / (1 - δ) :=
    mul_div_cancel_right₀ _ hσ.ne'
  rw [this]
  exact hball

end Branch

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.full_branch_embedded_orbit_of_morse_bott
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.embeddedCriticalOrbit_of_fullMode
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.tangent_iff_range_fderiv
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_slice_chart
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_ball_critical
