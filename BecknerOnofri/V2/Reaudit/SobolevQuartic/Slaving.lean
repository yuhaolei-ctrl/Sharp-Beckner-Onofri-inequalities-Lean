module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.Taylor
public import BecknerOnofri.LocalElevenCore.SobolevQuadraticTrustedBridge
public import BecknerOnofri.LocalElevenCore.ComplexFirstShellMoments

@[expose] public section

/-! # Part (b) of `lem:section5-quartic-reduction`, derived natively in `H^s`

`eq:section5-quadratic-slaving` and the first line of `eq:section5-complement-Taylor-expansions`:
the slaved complement `w(1, z)` equals the explicit quadratic term
`w_2(z) = ½ ((2π)^{-d}(-Δ)^{d/2} - Id)^{-1} P_{K^⊥}(v²)` up to `O(‖z‖³)` in the `H^s` norm.

Everything is carried out in the Banach algebra `Hs d s`:

1. the complement equation `w = P_{K^⊥} T (ρ_{v+w} - 1)` (`complementEq`, `τ = 1`) is expanded
   with the *native* second-order Taylor formula `Taylor.gibbs_second_order` for `ρ_u`;
2. `P_{K^⊥} T v = 0`, `P_{K^⊥} T 1 = 0`, and `w = O(‖z‖²)` (`graph_quadratic`, `D_v w(1,0) = 0`)
   give `(Id - P_{K^⊥} T) w = ½ P_{K^⊥} T (v²) + O(‖z‖³)`;
3. `Id - P_{K^⊥} T` is a Banach-space isomorphism of `K^⊥ ⊂ H^s` (`HsC.equiv`), so
   `w - w_2 = (Id - P_{K^⊥} T)^{-1} O(‖z‖³) = O(‖z‖³)` where `w_2 := ½ (Id - P_{K^⊥} T)^{-1}
   P_{K^⊥} T (v²)`.  Applying `T^{-1}` this is `(T^{-1} - Id) w_2 = ½ P_{K^⊥}(v²)`
   (`eq:section5-complement-order-two`), and `quadraticTermNative_coeff` computes the Fourier
   coefficients `1/(2(|k|^d - 1)) \widehat{v²}(k)` on `K^⊥`-frequencies.

No sup-norm graph is used: `graph_toComplement` is not invoked. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.V2.Reaudit.Sobolev BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell
  ContinuousComplement

variable {d : ℕ} {s : ℝ} [SobolevIndex d s]

/-- `D_v w(τ, 0) = 0` in the `H^s` norm: `w(τ, z) = O(‖z‖² + |τ-1| ‖z‖)` (native; analytic axis
bound for the `H^s` graph). -/
theorem graph_quadratic (hd11 : 11 ≤ d) :
    graph (s := s) hd11 =O[𝓝 (1, (0 : Coordinates d))]
      (fun x => ‖x.2‖ ^ 2 + |x.1 - 1| * ‖x.2‖) := by
  simpa only [Real.norm_eq_abs] using
    BecknerOnofri.analytic_axis_bound (graph_analytic hd11) (graph_derivative_zero hd11)
      (graph_axis hd11)

/-- `P_{K^⊥} T : H^s → K^⊥`, the Green-transformed projected operator
(`(2π)^d (-Δ)^{-d/2}` composed with `P_{K^⊥}`). -/
def cmG (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] HsC d s :=
  (Hs.complMap d s).comp (Hs.greenH d s)

@[simp] theorem cmG_apply (u : Hs d s) : cmG d s u = Hs.complMap d s (Hs.greenH d s u) := rfl

theorem cmG_one : cmG d s (1 : Hs d s) = 0 := by
  rw [cmG_apply, Hs.greenH_one, map_zero]

theorem cmG_assemblyH (z : Coordinates d) : cmG d s (Hs.assemblyH d s z) = 0 :=
  Hs.complMap_greenH_assemblyH z

theorem cmG_coe (w : HsC d s) : cmG d s (w : Hs d s) = HsC.linearPart d s w := rfl

/-- The Green-transformed quadratic source `½ P_{K^⊥} T (v²)` (right-hand side of
`eq:section5-complement-order-two` after applying `(2π)^d(-Δ)^{-d/2}`). -/
def quadraticSourceH (d : ℕ) (s : ℝ) [SobolevIndex d s] (z : Coordinates d) : HsC d s :=
  (1 / 2 : ℝ) • cmG d s ((Hs.assemblyH d s z) ^ 2)

/-- `w_2(z) = ½ (Id - P_{K^⊥} T)^{-1} P_{K^⊥} T (v²)`: the quadratic term of the slaved complement,
`eq:section5-quadratic-slaving`, as an element of `K^⊥ ⊂ H^s`. -/
def quadraticTermNative (hd11 : 11 ≤ d) (z : Coordinates d) : HsC d s :=
  (HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).symm (quadraticSourceH d s z)

/-- **`eq:section5-complement-order-two`** (Green-transformed form): `w_2 - P_{K^⊥} T w_2 =
½ P_{K^⊥} T (v²)`, i.e. `(T^{-1} - Id) w_2 = ½ P_{K^⊥}(v²)` after applying `T^{-1}`. -/
theorem quadraticTermNative_equation (hd11 : 11 ≤ d) (z : Coordinates d) :
    quadraticTermNative (s := s) hd11 z - HsC.linearPart d s (quadraticTermNative hd11 z) =
      quadraticSourceH d s z := by
  have h := (HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)).apply_symm_apply
    (quadraticSourceH d s z)
  rw [HsC.equiv_apply, one_smul] at h
  exact h

open Classical in
/-- Fourier coefficients of `w_2`: `\hat{w_2}(k) = 1/(2(|k|^d - 1)) \widehat{v²}(k)` for `k` in the
complement frequencies, `0` otherwise (`eq:section5-quadratic-slaving`). -/
theorem quadraticTermNative_coeff (hd11 : 11 ≤ d) (z : Coordinates d) (k : Frequency d) :
    coefficient k ((quadraticTermNative (s := s) hd11 z : HsC d s) : Hs d s).val =
      if ComplementFrequency k then
        ((1 / (2 * (frequencyLength k ^ d - 1)) : ℝ) : ℂ) * coefficient k (assembly d z ^ 2)
      else 0 := by
  have hinv : coefficient k ((quadraticTermNative (s := s) hd11 z : HsC d s) : Hs d s).val =
      (complementInverseMultiplier 1 k : ℂ) *
        coefficient k ((quadraticSourceH d s z : HsC d s) : Hs d s).val :=
    HsC.coeff_inverse (s := s) hd11 (μ := 1) (by norm_num) (by norm_num) _ k
  rw [hinv]
  by_cases hk : ComplementFrequency k
  · have hsrc : coefficient k ((quadraticSourceH d s z : HsC d s) : Hs d s).val =
        ((1 / 2 : ℝ) : ℂ) * (((1 / frequencyLength k ^ d : ℝ) : ℂ) * coefficient k (assembly d z ^ 2)) := by
      have h1 : ((quadraticSourceH d s z : HsC d s) : Hs d s).val =
          (1 / 2 : ℝ) • ((Hs.complMap d s (Hs.greenH d s ((Hs.assemblyH d s z) ^ 2)) : HsC d s) :
            Hs d s).val := rfl
      rw [h1, map_smul, Hs.coeff_complMap, Hs.coeff_greenH]
      simp only [hk, hk.1, ↓reduceIte, Complex.real_smul, val_pow', Hs.assemblyH_val]
    rw [hsrc]
    simp only [complementInverseMultiplier, hk, ↓reduceIte]
    have hEig := LocalEleven.complement_eigenvalue_ge_thirtytwo hd11 hk
    have h0 : frequencyLength k ^ d ≠ 0 := by linarith
    have h1 : frequencyLength k ^ d - 1 ≠ 0 := by linarith
    have hh : (1 - 1 / frequencyLength k ^ d)⁻¹ * (1 / 2 : ℝ) * (1 / frequencyLength k ^ d) =
        1 / (2 * (frequencyLength k ^ d - 1)) := by
      field_simp
    rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul, hh]
  · simp [complementInverseMultiplier, hk]

/-- The explicit quadratic term agrees with the explicit Fourier formula of
`LocalEleven.QuadraticSlaving.quadraticCorrection` (a finite-dimensional Fourier object, reused
only for the coefficient algebra; no graph is involved). -/
theorem toComplement_quadraticTermNative (hd11 : 11 ≤ d) (z : Coordinates d) :
    HsC.toComplement d s (quadraticTermNative (s := s) hd11 z) =
      LocalEleven.QuadraticSlaving.quadraticCorrection hd11 z := by
  classical
  apply Subtype.ext
  apply coefficient_ext
  intro k
  have h1 := quadraticTermNative_coeff (s := s) hd11 z k
  have h2 := LocalEleven.quadratic_slaving_coefficients hd11 z k
  rw [← coefficient_eq_fourierCoeff, ← coefficient_eq_fourierCoeff] at h2
  change coefficient k ((quadraticTermNative (s := s) hd11 z : HsC d s) : Hs d s).val = _
  rw [h1, h2]

/-! ## `D_v w(1, 0) = 0` in `H^s` and the expansion of the complement equation -/

theorem graph_one_isBigO (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => graph (s := s) hd11 (1, z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) := by
  have hz : Tendsto (fun z : Coordinates d => ((1 : ℝ), z)) (𝓝 0) (𝓝 (1, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
  have h := (graph_quadratic (s := s) hd11).comp_tendsto hz
  exact h.congr_right fun z => by simp

theorem graph_one_isBigO_one (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => graph (s := s) hd11 (1, z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
  (graph_one_isBigO hd11).trans (norm_pow_isBigO_of_le (m := 2) (n := 1) (by norm_num)
    |>.congr_right fun z => by simp)

/-- The third-order Gibbs remainder at the potential `U`. -/
def gibbsRem3 (U : Hs d s) : Hs d s :=
  Hs.gibbs U - 1 - U - (1 / 2 : ℝ) • (U ^ 2 - pk d s 2 U • (1 : Hs d s))

/-- **The complement equation to second order** (`τ = 1`), purely algebraic: if `w` solves
`w = P_{K^⊥} T (ρ_{v+w} - 1)` then
`(Id - P_{K^⊥} T)(w - w_2) = P_{K^⊥} T (v w + ½ w² + R_3(v+w))`,
where `R_3` is the third-order Gibbs remainder. -/
theorem equiv_sub_quadratic (hd11 : 11 ≤ d) (z : Coordinates d) (w : HsC d s)
    (hsol : complementEq d s 1 z w = 0) :
    HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num) (w - quadraticTermNative hd11 z) =
      cmG d s (Hs.assemblyH d s z * (w : Hs d s) + (1 / 2 : ℝ) • (w : Hs d s) ^ 2 +
        gibbsRem3 (Hs.assemblyH d s z + (w : Hs d s))) := by
  set v : Hs d s := Hs.assemblyH d s z with hv
  set U : Hs d s := v + (w : Hs d s) with hU
  have hw : w = cmG d s (Hs.gibbs U - 1) := by
    unfold complementEq at hsol
    rw [Hs.reconstructionH_apply, one_smul, sub_eq_zero] at hsol
    exact hsol
  have hdec : Hs.gibbs U - 1 = U + (1 / 2 : ℝ) • (U ^ 2 - pk d s 2 U • (1 : Hs d s)) + gibbsRem3 U := by
    unfold gibbsRem3
    abel
  have hsq : U ^ 2 = v ^ 2 + v * (w : Hs d s) + v * (w : Hs d s) + (w : Hs d s) ^ 2 := by
    rw [hU]; ring
  have hcU : cmG d s U = HsC.linearPart d s w := by
    rw [hU, map_add, hv, cmG_assemblyH, zero_add, cmG_coe]
  have hcU2 : cmG d s (U ^ 2) = cmG d s (v ^ 2) + cmG d s (v * (w : Hs d s)) +
      cmG d s (v * (w : Hs d s)) + cmG d s ((w : Hs d s) ^ 2) := by
    rw [hsq]; simp only [map_add]
  have hw' : w = HsC.linearPart d s w + (1 / 2 : ℝ) • cmG d s (v ^ 2) + cmG d s (v * (w : Hs d s)) +
      (1 / 2 : ℝ) • cmG d s ((w : Hs d s) ^ 2) + cmG d s (gibbsRem3 U) := by
    conv_lhs => rw [hw, hdec]
    simp only [map_add, map_smul, map_sub, hcU, hcU2, cmG_one, smul_zero, sub_zero]
    module
  have hq := quadraticTermNative_equation (s := s) hd11 z
  rw [HsC.equiv_apply, one_smul, map_sub]
  have : w - HsC.linearPart d s w - (quadraticTermNative hd11 z - HsC.linearPart d s (quadraticTermNative hd11 z)) =
      (w - HsC.linearPart d s w) - quadraticSourceH d s z := by rw [hq]
  have e : w - quadraticTermNative hd11 z - (HsC.linearPart d s w - HsC.linearPart d s (quadraticTermNative hd11 z)) =
      w - HsC.linearPart d s w - (quadraticTermNative hd11 z - HsC.linearPart d s (quadraticTermNative hd11 z)) := by
    abel
  rw [e, this, quadraticSourceH]
  simp only [map_add, map_smul]
  nth_rewrite 1 [hw']
  module

/-! ## The potential along the slice `τ = 1` -/

/-- `U(z) = v(z) + w(1, z) ∈ H^s`. -/
def slicePotentialH (hd11 : 11 ≤ d) (z : Coordinates d) : Hs d s :=
  Hs.reconstructionH d s (z, graph (s := s) hd11 (1, z))

theorem slicePotentialH_eq (hd11 : 11 ≤ d) (z : Coordinates d) :
    slicePotentialH (s := s) hd11 z =
      Hs.assemblyH d s z + ((graph (s := s) hd11 (1, z) : HsC d s) : Hs d s) := rfl

theorem slicePotentialH_mean (hd11 : 11 ≤ d) (z : Coordinates d) :
    Hs.meanCLM d s (slicePotentialH (s := s) hd11 z) = 0 :=
  Hs.meanCLM_reconstructionH _

theorem slicePotentialH_isBigO (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => slicePotentialH (s := s) hd11 z) =O[𝓝 (0 : Coordinates d)]
      (fun z => ‖z‖) := by
  have h1 : (fun z : Coordinates d => Hs.assemblyH d s z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
    (Hs.assemblyH d s).isBigO_id (𝓝 0) |>.norm_right
  have h2 := ((HsC d s).subtypeL.isBigO_comp (fun z : Coordinates d => graph (s := s) hd11 (1, z))
    (𝓝 0)).trans (graph_one_isBigO_one hd11)
  exact h1.add h2

theorem slicePotentialH_tendsto (hd11 : 11 ≤ d) :
    Tendsto (fun z : Coordinates d => slicePotentialH (s := s) hd11 z) (𝓝 0) (meanZeroNhds d s) := by
  have hz : Tendsto (fun z : Coordinates d => ((1 : ℝ), z)) (𝓝 0) (𝓝 (1, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
  have hg : Tendsto (fun z : Coordinates d => graph (s := s) hd11 (1, z)) (𝓝 0) (𝓝 0) := by
    have := ((graph_analytic (s := s) hd11).continuousAt.tendsto).comp hz
    rw [graph_base] at this
    exact this
  have h0 : Tendsto (fun z : Coordinates d => slicePotentialH (s := s) hd11 z) (𝓝 0) (𝓝 0) := by
    have := ((Hs.reconstructionH d s).continuous.tendsto (0, 0)).comp
      ((tendsto_id (α := Coordinates d)).prodMk_nhds hg)
    rw [show ((0 : Coordinates d), (0 : HsC d s)) = 0 from rfl, map_zero] at this
    exact this
  exact tendsto_nhdsWithin_iff.mpr ⟨h0, Eventually.of_forall (slicePotentialH_mean hd11)⟩

/-- **Part (b) of `lem:section5-quartic-reduction`, native in `H^s`.**  The slaved complement
`w(1, z)` of the `H^s` implicit-function graph equals the explicit quadratic term
`w_2(z) = ½ ((2π)^{-d}(-Δ)^{d/2} - Id)^{-1} P_{K^⊥}(v²)` (`quadraticTermNative`) up to
`O(‖z‖³)` in the `H^s` norm. -/
theorem graph_one_sub_quadratic (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => graph (s := s) hd11 (1, z) - quadraticTermNative hd11 z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
  have hz : Tendsto (fun z : Coordinates d => ((1 : ℝ), z)) (𝓝 0) (𝓝 (1, 0)) :=
    (continuous_const.prodMk continuous_id).tendsto' _ _ (by simp)
  set w : Coordinates d → HsC d s := fun z => graph (s := s) hd11 (1, z) with hwdef
  set v : Coordinates d → Hs d s := fun z => Hs.assemblyH d s z with hvdef
  have hv : v =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
    (Hs.assemblyH d s).isBigO_id (𝓝 0) |>.norm_right
  have hw2 : w =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) := graph_one_isBigO hd11
  have hwH2 : (fun z => (w z : Hs d s)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) :=
    ((HsC d s).subtypeL.isBigO_comp w (𝓝 0)).trans hw2
  -- the third-order remainder
  have hU := slicePotentialH_isBigO (s := s) hd11
  have hE3 : (fun z => gibbsRem3 (slicePotentialH (s := s) hd11 z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
    have h := (gibbs_second_order (d := d) (s := s)).comp_tendsto (slicePotentialH_tendsto hd11)
    exact h.trans (hU.norm_left.pow 3)
  -- the right-hand side of the second-order equation
  have hF : (fun z => v z * (w z : Hs d s) + (1 / 2 : ℝ) • (w z : Hs d s) ^ 2 +
      gibbsRem3 (slicePotentialH (s := s) hd11 z)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
    have a1 : (fun z => v z * (w z : Hs d s)) =O[𝓝 (0 : Coordinates d)]
        (fun z => ‖z‖ * ‖z‖ ^ 2) := hv.mul hwH2
    have a2 : (fun z => (w z : Hs d s) ^ 2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2 * ‖z‖ ^ 2) := by
      have := hwH2.mul hwH2
      exact this.congr_left fun z => (pow_two _).symm
    have a1' : (fun z => v z * (w z : Hs d s)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
      a1.congr_right fun z => by ring
    have a2' : (fun z => (w z : Hs d s) ^ 2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
      a2.trans ((norm_pow_isBigO_of_le (E := Coordinates d) (m := 4) (n := 3) (by norm_num)).congr_left
        fun z => by ring)
    exact (a1'.add (a2'.const_smul_left (1 / 2 : ℝ))).add hE3
  -- the inverse of `Id - P_{K^⊥} T` is bounded
  let e := HsC.equiv (s := s) hd11 (μ := 1) (by norm_num) (by norm_num)
  have hC : (fun z => cmG d s (v z * (w z : Hs d s) + (1 / 2 : ℝ) • (w z : Hs d s) ^ 2 +
      gibbsRem3 (slicePotentialH (s := s) hd11 z))) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
    ((cmG d s).isBigO_comp _ (𝓝 0)).trans hF
  have hS := (e.symm.toContinuousLinearMap.isBigO_comp _ (𝓝 (0 : Coordinates d))).trans hC
  have hsol := (graph_solves (s := s) hd11)
  have hsol' : ∀ᶠ z in 𝓝 (0 : Coordinates d), complementEq d s 1 z (w z) = 0 :=
    hz.eventually hsol
  refine hS.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hsol'] with z hz'
  have h := equiv_sub_quadratic (s := s) hd11 z (w z) hz'
  have h' : e (w z - quadraticTermNative hd11 z) = cmG d s (v z * (w z : Hs d s) +
      (1 / 2 : ℝ) • (w z : Hs d s) ^ 2 + gibbsRem3 (slicePotentialH (s := s) hd11 z)) := h
  change e.symm (cmG d s _) = _
  rw [← h']
  exact (e.symm_apply_apply _)

/-! ## The printed Taylor expansions `eq:section5-complement-Taylor-expansions` -/

theorem quadraticTermNative_smul (hd11 : 11 ≤ d) (t : ℝ) (z : Coordinates d) :
    quadraticTermNative (s := s) hd11 (t • z) = t ^ 2 • quadraticTermNative hd11 z := by
  unfold quadraticTermNative quadraticSourceH
  simp only [map_smul, smul_pow]
  exact smul_comm _ _ _

/-- First line of `eq:section5-complement-Taylor-expansions`: for fixed `v ∈ K` (i.e. fixed `z`),
`w(1, tv) = t² w_2(v) + O_{H^s}(t³)` as `t → 0`. -/
theorem graph_ray (hd11 : 11 ≤ d) (z : Coordinates d) :
    (fun t : ℝ => graph (s := s) hd11 (1, t • z) - t ^ 2 • quadraticTermNative hd11 z)
      =O[𝓝 (0 : ℝ)] (fun t => |t| ^ 3) := by
  have ht : Tendsto (fun t : ℝ => t • z) (𝓝 0) (𝓝 0) := by
    exact (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • z).tendsto' 0 0
      (by simp)
  have h := (graph_one_sub_quadratic (s := s) hd11).comp_tendsto ht
  refine (h.trans ?_).congr_left fun t => by simp [quadraticTermNative_smul]
  have : (fun t : ℝ => ‖t • z‖ ^ 3) = fun t => ‖z‖ ^ 3 * |t| ^ 3 := by
    funext t; rw [norm_smul, Real.norm_eq_abs, mul_pow]; ring
  simp only [Function.comp_def]
  rw [this]
  exact (isBigO_refl (fun t : ℝ => |t| ^ 3) _).const_mul_left (‖z‖ ^ 3)

/-- Pure algebra for the second line of `eq:section5-complement-Taylor-expansions`:
with `P = v ww + ½ ww²`, `ρ_{v+ww} - (1 + v + w_2 + ½(v² - ∫v²)) = R_3 + (ww - w_2) + (P - ∫P)`. -/
theorem slice_algebra (v ww w2 : Hs d s) :
    Hs.gibbs (v + ww) - (1 + v + w2 + (1 / 2 : ℝ) • (v ^ 2 - pk d s 2 v • (1 : Hs d s))) =
      gibbsRem3 (v + ww) + (ww - w2) +
        ((v * ww + (1 / 2 : ℝ) • ww ^ 2) -
          Hs.meanCLM d s (v * ww + (1 / 2 : ℝ) • ww ^ 2) • (1 : Hs d s)) := by
  have hsq : (v + ww) ^ 2 = v ^ 2 + (v * ww + (1 / 2 : ℝ) • ww ^ 2) + (v * ww + (1 / 2 : ℝ) • ww ^ 2) := by
    rw [show (v + ww) ^ 2 = v ^ 2 + (v * ww + v * ww) + ww ^ 2 by ring]
    module
  have hpk : pk d s 2 (v + ww) = pk d s 2 v + Hs.meanCLM d s (v * ww + (1 / 2 : ℝ) • ww ^ 2) +
      Hs.meanCLM d s (v * ww + (1 / 2 : ℝ) • ww ^ 2) := by
    unfold pk
    rw [hsq, map_add, map_add]
  unfold gibbsRem3
  rw [hpk, hsq]
  module

/-- **Second line of `eq:section5-complement-Taylor-expansions`, native in `H^s`**: along the
slice `τ = 1`,
`ρ_{v+w(1,v)} = 1 + v + w_2(v) + ½ (v² - ∫v²) + O_{H^s}(‖z‖³)`. -/
theorem gibbs_slice_expansion (hd11 : 11 ≤ d) :
    (fun z : Coordinates d => Hs.gibbs (slicePotentialH (s := s) hd11 z) -
        (1 + Hs.assemblyH d s z + ((quadraticTermNative hd11 z : HsC d s) : Hs d s) +
          (1 / 2 : ℝ) • ((Hs.assemblyH d s z) ^ 2 -
            pk d s 2 (Hs.assemblyH d s z) • (1 : Hs d s))))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
  set w : Coordinates d → HsC d s := fun z => graph (s := s) hd11 (1, z) with hwdef
  have hv : (fun z : Coordinates d => Hs.assemblyH d s z) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖) :=
    (Hs.assemblyH d s).isBigO_id (𝓝 0) |>.norm_right
  have hw2 : w =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) := graph_one_isBigO hd11
  have hwH2 : (fun z => (w z : Hs d s)) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 2) :=
    ((HsC d s).subtypeL.isBigO_comp w (𝓝 0)).trans hw2
  have hU := slicePotentialH_isBigO (s := s) hd11
  have hE3 : (fun z => gibbsRem3 (slicePotentialH (s := s) hd11 z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
    have h := (gibbs_second_order (d := d) (s := s)).comp_tendsto (slicePotentialH_tendsto hd11)
    exact h.trans (hU.norm_left.pow 3)
  have hD1 : (fun z => ((w z - quadraticTermNative hd11 z : HsC d s) : Hs d s))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
    ((HsC d s).subtypeL.isBigO_comp _ (𝓝 0)).trans (graph_one_sub_quadratic hd11)
  have hP : (fun z => Hs.assemblyH d s z * (w z : Hs d s) + (1 / 2 : ℝ) • (w z : Hs d s) ^ 2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) := by
    have a1 := hv.mul hwH2
    have a2 := hwH2.mul hwH2
    have a1' : (fun z => Hs.assemblyH d s z * (w z : Hs d s)) =O[𝓝 (0 : Coordinates d)]
        (fun z => ‖z‖ ^ 3) := a1.congr_right fun z => by ring
    have a2' : (fun z => (w z : Hs d s) ^ 2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖ ^ 3) :=
      (a2.congr_left fun z => (pow_two _).symm).trans
        ((norm_pow_isBigO_of_le (E := Coordinates d) (m := 4) (n := 3) (by norm_num)).congr_left
          fun z => by ring)
    exact a1'.add (a2'.const_smul_left (1 / 2 : ℝ))
  have hmP : (fun z => Hs.meanCLM d s (Hs.assemblyH d s z * (w z : Hs d s) +
      (1 / 2 : ℝ) • (w z : Hs d s) ^ 2) • (1 : Hs d s)) =O[𝓝 (0 : Coordinates d)]
        (fun z => ‖z‖ ^ 3) := by
    have := ((Hs.meanCLM d s).isBigO_comp _ (𝓝 (0 : Coordinates d))).trans hP
    have h1 := this.smul (isBigO_const_const (1 : Hs d s) (one_ne_zero' (ℝ)) (𝓝 (0 : Coordinates d)))
    simpa using h1
  refine ((hE3.add hD1).add (hP.sub hmP)).congr_left fun z => ?_
  exact (slice_algebra (Hs.assemblyH d s z) (w z : Hs d s)
    ((quadraticTermNative hd11 z : HsC d s) : Hs d s)).symm

theorem smul_tendsto_zero (z : Coordinates d) :
    Tendsto (fun t : ℝ => t • z) (𝓝 0) (𝓝 0) :=
  (continuous_id.smul continuous_const : Continuous fun t : ℝ => t • z).tendsto' 0 0 (by simp)

/-- **`eq:section5-complement-Taylor-expansions`, both lines, exactly as printed** (fixed
`v ∈ K`, i.e. fixed `z`, `t → 0`, remainders in the `H^s` norm):
`ρ_{tv + w(1,tv)} = 1 + tv + t² (w_2(v) + ½ v² - ½ ∫v²) + O_{H^s}(t³)`. -/
theorem gibbs_ray (hd11 : 11 ≤ d) (z : Coordinates d) :
    (fun t : ℝ => Hs.gibbs (slicePotentialH (s := s) hd11 (t • z)) -
        (1 + t • Hs.assemblyH d s z + t ^ 2 • (((quadraticTermNative hd11 z : HsC d s) : Hs d s) +
          (1 / 2 : ℝ) • ((Hs.assemblyH d s z) ^ 2 - pk d s 2 (Hs.assemblyH d s z) • (1 : Hs d s)))))
      =O[𝓝 (0 : ℝ)] (fun t => |t| ^ 3) := by
  have h := (gibbs_slice_expansion (s := s) hd11).comp_tendsto
    (smul_tendsto_zero z)
  refine (h.trans ?_).congr_left fun t => ?_
  · have : (fun t : ℝ => ‖t • z‖ ^ 3) = fun t => ‖z‖ ^ 3 * |t| ^ 3 := by
      funext t; rw [norm_smul, Real.norm_eq_abs, mul_pow]; ring
    simp only [Function.comp_def]
    rw [this]
    exact (isBigO_refl (fun t : ℝ => |t| ^ 3) _).const_mul_left (‖z‖ ^ 3)
  · simp only [Function.comp_apply, map_smul, quadraticTermNative_smul, smul_pow, pk_smul,
      Submodule.coe_smul]
    module

end BecknerOnofri.V2.Reaudit.SobolevQuartic
