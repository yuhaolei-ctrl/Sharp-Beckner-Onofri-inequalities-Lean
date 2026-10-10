module

public import BecknerOnofri.V2.Reaudit.MorseBott.EmbeddedOrbit
public import BecknerOnofri.LocalElevenCore.SupportedFamilyStability

@[expose] public section

/-! # Embedded critical manifold of the full branch: instantiation

Glue only.  `SupportedFamily.full_branch_morse_bott` (existing, reused) supplies `FullModeMorseBott`
for the full-support branch; its proof imports the legacy local-maximality chain, which is why this
instantiation lives in a separate module from the new geometric content. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.MorseBott
open BecknerOnofri.HighDim BecknerOnofri.HighDim.LocalEleven

/-- **Embedded Morse--Bott critical manifold of the full-support branch.**  For `11 ≤ d`, `s > d/2`
and all sufficiently small `δ > 0`, the full-support branch `u_δ = branch univ δ` at coupling
`β = β_s(d)/(1-δ)` satisfies the existing `FullModeMorseBott` and, in addition, the exact geometric
statement `EmbeddedCriticalOrbit`. -/
theorem full_branch_embedded_orbit {d : ℕ} (hd : 11 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 < s) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∃ hu : InSobolev s (SupportedFamily.branch hd Finset.univ δ),
        FullModeMorseBott ((1 / (1 - δ)) * spectralThreshold d)
          (SupportedFamily.branch hd Finset.univ δ) ∧
        EmbeddedCriticalOrbit ((1 / (1 - δ)) * spectralThreshold d) s
          (SupportedFamily.branch hd Finset.univ δ) hu := by
  filter_upwards [SupportedFamily.full_branch_morse_bott hd,
    full_branch_embedded_orbit_of_morse_bott hd hs (SupportedFamily.full_branch_morse_bott hd)]
    with δ hmb ⟨hu, hE⟩
  exact ⟨hu, hmb, hE⟩

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.full_branch_embedded_orbit
