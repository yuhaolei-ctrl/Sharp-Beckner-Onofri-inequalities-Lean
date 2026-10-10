module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Slaving
public import BecknerOnofri.LocalQuarticStatementDefinitions
public import BecknerOnofri.LocalElevenCore.SlavedMoments
public import BecknerOnofri.LocalElevenCore.ReducedQuarticExpansion

@[expose] public section

/-! # Part (c) of `lem:section5-quartic-reduction` at `τ = 1`, native in `H^s`

The reduced functional on the slice `τ = 1`,
`Θ(1, z) = log Z(v + w) - S - ½ ∫ w ρ_{v+w}`
(the Euler form of `Φ_{d,1}(v + w(1,v)) = log Z(u) - ½‖u‖²_{Ḣ^{d/2}}`, see `Euler.lean`), is expanded to
fourth order with the *native* `H^s` ingredients

* `Taylor.logZ_taylor` (`eq:section5-log-partition-taylor`),
* `Slaving.graph_one_sub_quadratic` (`w = w_2 + O(‖z‖³)`),
* `Slaving.gibbs_slice_expansion` (`ρ_{v+w} = 1 + v + w_2 + ½(v² - ∫v²) + O(‖z‖³)`),

and the orthogonality relations `∫ v w = 0`, `∫ w = 0`, `∫ v³ = 0`.  The result is

`Θ(1,z) = ¼ ∫ v² w_2 + (1/24) ∫ v⁴ - ⅛ (∫ v²)² + O(‖z‖⁵)`,

which is the quartic of `eq:section5-quartic-form` by the (reused, finite-dimensional)
Schur-complement identity of `QuadraticModes`/`ComplexFirstShellMoments`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-! ## Orthogonality relations in `H^s` -/

theorem meanCLM_coe_complement (w : HsC d s) : Hs.meanCLM d s (w : Hs d s) = 0 := by
  rw [Hs.meanCLM_apply]
  exact w.property.1

/-- `∫ v w = 0` for `v ∈ K`, `w ∈ K^⊥` (Haar orthogonality of the first shell and its
complement). -/
theorem meanCLM_assemblyH_mul (z : Coordinates d) (w : HsC d s) :
    Hs.meanCLM d s (Hs.assemblyH d s z * (w : Hs d s)) = 0 := by
  have h := BecknerOnofri.HighDim.LocalEleven.SlavedMoments.mean_mul_assembly
    (HsC.toComplement d s w) z
  rw [Hs.meanCLM_apply, Hs.val_mul, Hs.assemblyH_val, mul_comm]
  exact h

theorem pk_two_assemblyH (z : Coordinates d) :
    pk d s 2 (Hs.assemblyH d s z) = 2 * LocalReductionStatement.mass z := by
  unfold pk
  rw [Hs.meanCLM_apply, val_pow', Hs.assemblyH_val]
  exact BecknerOnofri.HighDim.LocalEleven.GraphEnergy.assembly_square_mean z

theorem pk_three_assemblyH (z : Coordinates d) : pk d s 3 (Hs.assemblyH d s z) = 0 := by
  unfold pk
  rw [Hs.meanCLM_apply, val_pow', Hs.assemblyH_val]
  exact BecknerOnofri.HighDim.LocalEleven.QuadraticModes.assembly_third_moment z

theorem isBigO_meanCLM {α : Type*} {l : Filter α} {f : α → Hs d s} {g : α → ℝ}
    (h : f =O[l] g) : (fun x => Hs.meanCLM d s (f x)) =O[l] g :=
  ((Hs.meanCLM d s).isBigO_comp f l).trans h

/-! ## Moment algebra -/

theorem pk_two_split (v w : Hs d s) (hvw : Hs.meanCLM d s (v * w) = 0) :
    pk d s 2 (v + w) = pk d s 2 v + Hs.meanCLM d s (w * w) := by
  unfold pk
  have e : (v + w) ^ 2 = v ^ 2 + (v * w + v * w) + w * w := by ring
  rw [e]
  simp only [map_add]
  rw [hvw]
  ring

theorem pk_three_split (v w w2 : Hs d s) (h3 : pk d s 3 v = 0) :
    pk d s 3 (v + w) - 3 * Hs.meanCLM d s (v ^ 2 * w2) =
      3 * Hs.meanCLM d s (v * v * (w - w2)) + 3 * Hs.meanCLM d s (v * (w * w)) +
        Hs.meanCLM d s (w * w * w) := by
  have e : (v + w) ^ 3 = v ^ 3 + (v * v * w + v * v * w + v * v * w) +
      (v * (w * w) + v * (w * w) + v * (w * w)) + w * w * w := by ring
  have e2 : v * v * (w - w2) = v * v * w - v ^ 2 * w2 := by ring
  unfold pk at *
  rw [e, e2]
  simp only [map_add, map_sub]
  linarith

theorem pk_four_split (v w : Hs d s) :
    pk d s 4 (v + w) - pk d s 4 v =
      Hs.meanCLM d s (w * ((v + w) ^ 3 + (v + w) ^ 2 * v + (v + w) * v ^ 2 + v ^ 3)) := by
  unfold pk
  rw [← map_sub]
  congr 1
  ring

/-- Pairing of `w ∈ K^⊥` against the third-order Gibbs density. -/
theorem rho_pairing (v w w2 R : Hs d s) (hw : Hs.meanCLM d s w = 0)
    (hvw : Hs.meanCLM d s (v * w) = 0) :
    Hs.meanCLM d s (w * (1 + v + w2 + (1 / 2 : ℝ) • (v ^ 2 - pk d s 2 v • (1 : Hs d s)) + R)) =
      Hs.meanCLM d s (w * w2) + (1 / 2 : ℝ) * Hs.meanCLM d s (w * v ^ 2) +
        Hs.meanCLM d s (w * R) := by
  have e : w * (1 + v + w2 + (1 / 2 : ℝ) • (v ^ 2 - pk d s 2 v • (1 : Hs d s)) + R) =
      w + v * w + w * w2 + (1 / 2 : ℝ) • (w * v ^ 2) - ((1 / 2 : ℝ) * pk d s 2 v) • w + w * R := by
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one, smul_sub, smul_smul]
    rw [mul_comm w v]
    abel
  rw [e]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hw, hvw]
  ring

/-! ## The reduced functional in Euler form -/

/-- The Euler form of the reduced functional: for `w ∈ K^⊥` and the first-shell parameter `z`,
`L_z(w) = log Z(v + w) - S - ½ ∫ w ρ_{v+w}`, `S = Σ |z_j|²`. -/
def Lfun (z : Coordinates d) (w : Hs d s) : ℝ :=
  logZ (Hs.assemblyH d s z + w) - LocalReductionStatement.mass z -
    (1 / 2 : ℝ) * Hs.meanCLM d s (w * Hs.gibbs (Hs.assemblyH d s z + w))

/-- `Θ(τ, z) = L_z(w(τ, z))`, i.e. `Φ_{d,τ}(v + w(τ,v)) - (1 - 1/τ) S` (Euler form). -/
def Theta (hd11 : 11 ≤ d) (x : ℝ × Coordinates d) : ℝ :=
  Lfun x.2 ((graph (s := s) hd11 x : HsC d s) : Hs d s)

/-! ## The expansion at `τ = 1` -/

section Slice

variable (hd11 : 11 ≤ d)

/-- `w(1, z) ∈ K^⊥ ⊂ H^s`. -/
def wS (z : Coordinates d) : Hs d s := ((graph (s := s) hd11 (1, z) : HsC d s) : Hs d s)

/-- `w_2(z) ∈ K^⊥ ⊂ H^s`. -/
def w2S (z : Coordinates d) : Hs d s := ((quadraticTermNative (s := s) hd11 z : HsC d s) : Hs d s)

theorem wS_isBigO : (fun z : Coordinates d => wS (s := s) hd11 z) =O[𝓝 0] (fun z => ‖z‖ ^ 2) :=
  ((HsC d s).subtypeL.isBigO_comp _ (𝓝 0)).trans (graph_one_isBigO hd11)

theorem wS_sub_w2S : (fun z : Coordinates d => wS (s := s) hd11 z - w2S hd11 z)
    =O[𝓝 0] (fun z => ‖z‖ ^ 3) := by
  refine (((HsC d s).subtypeL.isBigO_comp _ (𝓝 0)).trans (graph_one_sub_quadratic hd11)).congr_left
    fun z => ?_
  rfl

theorem w2S_isBigO : (fun z : Coordinates d => w2S (s := s) hd11 z) =O[𝓝 0] (fun z => ‖z‖ ^ 2) := by
  have h := (wS_isBigO hd11).sub ((wS_sub_w2S (s := s) hd11).trans
    (norm_pow_isBigO_of_le (E := Coordinates d) (m := 3) (n := 2) (by norm_num)))
  exact h.congr_left fun z => by abel

theorem assemblyH_isBigO : (fun z : Coordinates d => Hs.assemblyH d s z) =O[𝓝 0] (fun z => ‖z‖) :=
  (Hs.assemblyH d s).isBigO_id (𝓝 0) |>.norm_right

/-- `U(1,z) = v + w(1,z)` -/
theorem slicePotentialH_eq' (z : Coordinates d) :
    slicePotentialH (s := s) hd11 z = Hs.assemblyH d s z + wS hd11 z := rfl

/-- **The fourth-order expansion of the reduced functional at `τ = 1`** (native `H^s`
version of the computation after `eq:section5-log-partition-taylor`):
`Θ(1,z) = ¼ ∫ v² w_2 + (1/24)∫ v⁴ - ⅛ (∫ v²)² + O(‖z‖⁵)`. -/
theorem theta_one_expansion :
    (fun z : Coordinates d => Lfun z (wS (s := s) hd11 z) -
      ((1 / 4 : ℝ) * Hs.meanCLM d s (Hs.assemblyH d s z ^ 2 * w2S hd11 z) +
        pk d s 4 (Hs.assemblyH d s z) / 24 - (pk d s 2 (Hs.assemblyH d s z)) ^ 2 / 8))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) := by
  set v : Coordinates d → Hs d s := fun z => Hs.assemblyH d s z with hvdef
  set w : Coordinates d → Hs d s := fun z => wS (s := s) hd11 z with hwdef
  set w2 : Coordinates d → Hs d s := fun z => w2S (s := s) hd11 z with hw2def
  set U : Coordinates d → Hs d s := fun z => slicePotentialH (s := s) hd11 z with hUdef
  set ρ : Coordinates d → Hs d s := fun z => Hs.gibbs (U z) with hρdef
  set m : Hs d s →L[ℝ] ℝ := Hs.meanCLM d s with hm
  have hv : v =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := assemblyH_isBigO
  have hw : w =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) := wS_isBigO hd11
  have hw3 : (fun z => w z - w2 z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := wS_sub_w2S hd11
  have hw2 : w2 =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) := w2S_isBigO hd11
  have hU : U =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) := slicePotentialH_isBigO hd11
  -- the Gibbs density to third order
  set ρ0 : Coordinates d → Hs d s := fun z =>
    1 + v z + w2 z + (1 / 2 : ℝ) • (v z ^ 2 - pk d s 2 (v z) • (1 : Hs d s)) with hρ0
  have hR : (fun z => ρ z - ρ0 z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
    gibbs_slice_expansion hd11
  -- powers of `‖z‖`
  have p2 : (fun z : Coordinates d => ‖z‖ ^ 2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) :=
    isBigO_refl _ _
  have lower : ∀ {a b : ℕ}, b ≤ a → (fun z : Coordinates d => ‖z‖ ^ a) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖ ^ b) := fun h => norm_pow_isBigO_of_le h
  -- error terms
  -- E1: Taylor remainder of `log Z`
  have E1 : (fun z => logZ (U z) - (pk d s 2 (U z) / 2 + pk d s 3 (U z) / 6 + pk d s 4 (U z) / 24 -
      (pk d s 2 (U z)) ^ 2 / 8)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
    (logZ_taylor (d := d) (s := s)).comp_tendsto (slicePotentialH_tendsto hd11) |>.trans
      (hU.norm_left.pow 5)
  -- the quadratic moment of `w`
  have hww : (fun z => w z * w z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2 * ‖z‖ ^ 2) := hw.mul hw
  have hww' : (fun z => w z * w z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 4) :=
    hww.congr_right fun z => by ring
  -- E2
  have E2 : (fun z => (m (w z * w z) - m (w2 z * w2 z))) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖ ^ 5) := by
    have h := isBigO_meanCLM ((hw3.mul (hw.add hw2)))
    refine (h.congr_left fun z => ?_).congr_right fun z => by ring
    simp only [← map_sub]
    congr 1
    ring
  have hUeq : ∀ z, U z = v z + w z := fun z => rfl
  have hm_w : ∀ z, m (w z) = 0 := fun z => meanCLM_coe_complement _
  have hm_vw : ∀ z, m (v z * w z) = 0 := fun z => meanCLM_assemblyH_mul z _
  have hU2 : ∀ z, pk d s 2 (U z) = pk d s 2 (v z) + m (w z * w z) := fun z => by
    rw [hUeq]; exact pk_two_split _ _ (hm_vw z)
  -- E3
  have E3 : (fun z => pk d s 3 (U z) - 3 * m (v z ^ 2 * w2 z)) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖ ^ 5) := by
    have a1 := isBigO_meanCLM ((hv.mul hv).mul hw3)
    have a2 := isBigO_meanCLM (hv.mul hww')
    have a3 := isBigO_meanCLM (hww'.mul hw)
    have a1' : (fun z => m (v z * v z * (w z - w2 z))) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      a1.congr_right fun z => by ring
    have a2' : (fun z => m (v z * (w z * w z))) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      a2.congr_right fun z => by ring
    have a3' : (fun z => m (w z * w z * w z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      (a3.congr_right (g₂ := fun z : Coordinates d => ‖z‖ ^ 6) fun z => by ring).trans (lower (by norm_num))
    refine (((a1'.const_mul_left 3).add (a2'.const_mul_left 3)).add a3').congr_left fun z => ?_
    rw [hUeq]
    exact (pk_three_split _ _ _ (pk_three_assemblyH z)).symm
  -- E4
  have E4 : (fun z => pk d s 4 (U z) - pk d s 4 (v z)) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖ ^ 5) := by
    have b1 : (fun z => U z ^ 3 + U z ^ 2 * v z + U z * v z ^ 2 + v z ^ 3) =O[𝓝 (0 : Coordinates d)]
        (fun z => ‖z‖ ^ 3) := by
      have c1 := hU.pow 3
      have c2 := (hU.pow 2).mul hv
      have c3 := hU.mul (hv.pow 2)
      have c4 := hv.pow 3
      refine ((c1.add (c2.congr_right fun z => by ring)).add (c3.congr_right fun z => by ring)).add c4
    have := isBigO_meanCLM (hw.mul b1)
    refine (this.congr_right fun z => by ring).congr_left fun z => ?_
    rw [hUeq]
    exact (pk_four_split _ _).symm
  -- E5
  have hpk2v : (fun z => pk d s 2 (v z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) :=
    ((isBigO_meanCLM (hv.mul hv)).congr_left fun z => by simp [pk, sq]).congr_right
      fun z => by ring
  have E5 : (fun z => (pk d s 2 (U z)) ^ 2 - (pk d s 2 (v z)) ^ 2) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖ ^ 5) := by
    have hb : (fun z => m (w z * w z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 4) :=
      isBigO_meanCLM hww'
    have hb2 : (fun z => m (w z * w z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) :=
      hb.trans (lower (by norm_num))
    have h := hb.mul ((hpk2v.const_mul_left 2).add hb2)
    refine (h.trans ?_).congr_left fun z => ?_
    · have : (fun z : Coordinates d => ‖z‖ ^ 4 * ‖z‖ ^ 2) = fun z => ‖z‖ ^ 6 := by
        funext z; ring
      rw [this]
      exact lower (by norm_num)
    · simp only [hU2]
      ring
  -- E6
  have E6 : (fun z => m (w z * ρ z) - (m (w2 z * w2 z) + (1 / 2 : ℝ) * m (v z ^ 2 * w2 z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) := by
    have a1 := isBigO_meanCLM (hw3.mul hw2)
    have a2 := isBigO_meanCLM (hw3.mul (hv.pow 2))
    have a3 := isBigO_meanCLM (hw.mul hR)
    have a1' : (fun z => m ((w z - w2 z) * w2 z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      a1.congr_right fun z => by ring
    have a2' : (fun z => m ((w z - w2 z) * v z ^ 2)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      a2.congr_right fun z => by ring
    have a3' : (fun z => m (w z * (ρ z - ρ0 z))) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
      a3.congr_right fun z => by ring
    refine ((a1'.add (a2'.const_mul_left (1 / 2 : ℝ))).add a3').congr_left fun z => ?_
    have hr := rho_pairing (v z) (w z) (w2 z) (ρ z - ρ0 z) (hm_w z) (hm_vw z)
    have hρz : ρ z = 1 + v z + w2 z + (1 / 2 : ℝ) • (v z ^ 2 - pk d s 2 (v z) • (1 : Hs d s)) +
        (ρ z - ρ0 z) := by
      simp only [hρ0]; abel
    have hmain : m (w z * ρ z) = m (w z * w2 z) + (1 / 2 : ℝ) * m (w z * v z ^ 2) +
        m (w z * (ρ z - ρ0 z)) := by
      rw [← hr, ← hρz]
    rw [hmain]
    simp only [mul_sub, sub_mul, map_sub]
    rw [mul_comm (w z) (w2 z), mul_comm (w z) (v z ^ 2), mul_comm (w2 z) (v z ^ 2)]
    ring
  -- assemble
  have hsum := ((((E1.add (E2.const_mul_left (1 / 2 : ℝ))).add (E3.const_mul_left (1 / 6 : ℝ))).add
    (E4.const_mul_left (1 / 24 : ℝ))).sub (E5.const_mul_left (1 / 8 : ℝ))).sub
    (E6.const_mul_left (1 / 2 : ℝ))
  refine hsum.congr_left fun z => ?_
  have hmass : LocalReductionStatement.mass z = pk d s 2 (v z) / 2 := by
    rw [show v z = Hs.assemblyH d s z from rfl, pk_two_assemblyH]; ring
  have hL : Lfun z (wS (s := s) hd11 z) =
      logZ (U z) - pk d s 2 (v z) / 2 - 1 / 2 * m (w z * ρ z) := by
    unfold Lfun; rw [hmass]; rfl
  have hT : ((1 / 4 : ℝ) * Hs.meanCLM d s (Hs.assemblyH d s z ^ 2 * w2S hd11 z) +
      pk d s 4 (Hs.assemblyH d s z) / 24 - (pk d s 2 (Hs.assemblyH d s z)) ^ 2 / 8) =
      (1 / 4 : ℝ) * m (v z ^ 2 * w2 z) + pk d s 4 (v z) / 24 - (pk d s 2 (v z)) ^ 2 / 8 := rfl
  rw [hL, hT]
  have h2 := hU2 z
  linear_combination (-(1 / 2 : ℝ)) * h2

end Slice

/-- The moment expression of the quartic equals the printed quartic form
`a_d Σ|z_j|⁴ + b_d Σ_{i<j}|z_i|²|z_j|²` (`eq:section5-quartic-form`): the reused finite-dimensional
Schur-complement identity (`QuadraticModes.actual_quartic_coefficients`,
`ReducedQuarticExpansion.pairing_quadraticCorrection`) together with
`quadraticTermNative = ι⁻¹ quadraticCorrection`. -/
theorem quartic_moments_eq (hd11 : 11 ≤ d) (z : Coordinates d) :
    (1 / 4 : ℝ) * Hs.meanCLM d s (Hs.assemblyH d s z ^ 2 * w2S (s := s) hd11 z) +
      pk d s 4 (Hs.assemblyH d s z) / 24 - (pk d s 2 (Hs.assemblyH d s z)) ^ 2 / 8 =
      LocalReductionStatement.quartic z := by
  have hq := BecknerOnofri.HighDim.LocalEleven.QuadraticModes.actual_quartic_coefficients hd11 z
  rw [← BecknerOnofri.HighDim.LocalEleven.ReducedQuarticExpansion.pairing_quadraticCorrection
    hd11 z] at hq
  have hqc : (LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z : Space d) =
      (w2S (s := s) hd11 z).val := by
    rw [← toComplement_quadraticTermNative (s := s) hd11 z]; rfl
  rw [hqc] at hq
  have e4 : pk d s 4 (Hs.assemblyH d s z) = mean d ((assembly d z) ^ 4) := by
    unfold pk; rw [Hs.meanCLM_apply, val_pow', Hs.assemblyH_val]
  have e2 : pk d s 2 (Hs.assemblyH d s z) = mean d ((assembly d z) ^ 2) := by
    unfold pk; rw [Hs.meanCLM_apply, val_pow', Hs.assemblyH_val]
  have e1 : Hs.meanCLM d s (Hs.assemblyH d s z ^ 2 * w2S (s := s) hd11 z) =
      mean d (BecknerOnofri.HighDim.LocalEleven.SlavedMoments.V d z ^ 2 * (w2S (s := s) hd11 z).val) := by
    rw [Hs.meanCLM_apply, Hs.val_mul, val_pow', Hs.assemblyH_val]
  rw [e4, e2, e1]
  have : LocalReductionStatement.quartic z =
      quarticA d * (∑ i : Fin d, ‖z i‖ ^ 4) +
        quarticB d * BecknerOnofri.HighDim.LocalEleven.QuadraticModes.mixedAmplitudeSum z := rfl
  rw [this, ← hq]
  ring

/-- **Fourth-order expansion at `τ = 1` with the printed quartic**:
`Θ(1,z) = Q_{4,d}(z) + O(‖z‖⁵)`. -/
theorem theta_one_quartic (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => Lfun z (wS (s := s) hd11 z) - LocalReductionStatement.quartic z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 5) :=
  (theta_one_expansion (s := s) hd11).congr_left fun z => by rw [quartic_moments_eq]


end BecknerOnofri.V2.Reaudit.SobolevQuartic
