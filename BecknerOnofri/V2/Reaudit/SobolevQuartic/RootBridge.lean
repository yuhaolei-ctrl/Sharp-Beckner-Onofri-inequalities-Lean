module

public import BecknerOnofri.V2.Reaudit.SobolevQuartic.CoreBridge
public import BecknerOnofri.ReducedEnergyJointExpansion
public import BecknerOnofri.GreenLocalBranch

@[expose] public section

/-! # The root (`12 ≤ d`) joint quartic expansion, from the native `H^s` reduction (S054, W-b)

The root copy of the reduced-energy development (`HighDim.GreenLocalBranch`, `HighDim.ReducedEquation`,
`HighDim.ReducedEnergyGradient`) and the Core copy (`HighDim.LocalEleven.*`, whose `correction` is the
Sobolev graph) solve the same equation `projectedEquation = 0` near `(1, 0)`; both corrections are the
unique local solution, hence agree near `(1, 0)` (`correction_eq_core`).  Consequently the root
`physicalReducedEnergy` agrees with the Core one, and the root two-parameter expansion
`physicalReducedEnergy_joint_quartic` is recovered from the Core expansion
`physicalReducedEnergy_quartic_paper_native` (proved from `section5_quartic_reduction_native`) by
`‖z‖² ≤ S ≤ d ‖z‖²` and `|1 - 1/τ| ≤ 2 |τ - 1|` near `τ = 1`.  The statement of
`physicalReducedEnergy_joint_quartic_native` is exactly that of the root
`UniformComplementBounds.physicalReducedEnergy_joint_quartic`. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators

namespace BecknerOnofri.V2.Reaudit.SobolevQuartic
open BecknerOnofri.HighDim ContinuousFirstShell ContinuousComplement

/-- The root `GreenLocalBranch.correction` and the Core one (the Sobolev graph) agree near `(1, 0)`. -/
theorem correction_eq_core {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      GreenLocalBranch.correction hd x = LocalEleven.GreenLocalBranch.correction (by omega) x := by
  have hd11 : 11 ≤ d := by omega
  have hc : ContinuousAt (LocalEleven.GreenLocalBranch.correction hd11) (1, 0) :=
    (LocalEleven.GreenLocalBranch.correction_analytic hd11).continuousAt
  have hc' : Tendsto (fun x : ℝ × Coordinates d => (x, LocalEleven.GreenLocalBranch.correction hd11 x))
      (𝓝 (1, 0)) (𝓝 ((1, (0 : Coordinates d)), (0 : complement d))) := by
    have h := continuousAt_id.prodMk hc
    simpa [LocalEleven.GreenLocalBranch.correction_base] using h.tendsto
  filter_upwards [hc'.eventually (GreenLocalBranch.correction_unique hd),
    LocalEleven.GreenLocalBranch.correction_solves hd11] with x hu hs
  exact hu.mp hs

theorem physicalReducedEnergy_eq_core {d : ℕ} (hd : 12 ≤ d) :
    ∀ᶠ x in 𝓝 (1, (0 : Coordinates d)),
      ReducedEnergyGradient.physicalReducedEnergy hd x =
        LocalEleven.ReducedEnergyGradient.physicalReducedEnergy (by omega) x := by
  filter_upwards [correction_eq_core hd] with x hx
  simp only [ReducedEnergyGradient.physicalReducedEnergy, LocalEleven.ReducedEnergyGradient.physicalReducedEnergy,
    ReducedEquation.potential, LocalEleven.ReducedEquation.potential, hx]

theorem delta_inv_le : ∀ᶠ μ : ℝ in 𝓝 1, |1 - 1 / μ| ≤ 2 * |μ - 1| := by
  filter_upwards [Icc_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2)] with μ hμ
  have hp : 0 < μ := by linarith [hμ.1]
  have he : 1 - 1 / μ = (μ - 1) / μ := by field_simp
  rw [he, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have : 0 ≤ |μ - 1| := abs_nonneg _
  nlinarith [hμ.1]

theorem squaredAmplitude_le_card {d : ℕ} (z : Coordinates d) :
    LocalEleven.UniformComplementBounds.squaredAmplitude z ≤ (d : ℝ) * ‖z‖ ^ 2 := by
  unfold LocalEleven.UniformComplementBounds.squaredAmplitude
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin d, ‖z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z i) 2
    _ = (d : ℝ) * ‖z‖ ^ 2 := by simp

/-- **Root joint quartic expansion, native route.**  Same statement as the root
`UniformComplementBounds.physicalReducedEnergy_joint_quartic`; proved from the Core expansion
`physicalReducedEnergy_quartic_paper_native` (hence from `section5_quartic_reduction_native`). -/
theorem physicalReducedEnergy_joint_quartic_native {d : ℕ} (hd : 12 ≤ d) :
    (fun x : ℝ × Coordinates d => ReducedEnergyGradient.physicalReducedEnergy hd x -
        (1 - 1 / x.1) * (∑ i : Fin d, ‖x.2 i‖ ^ 2) - ReducedQuarticExpansion.quarticValue x.2)
      =O[𝓝 (1, (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 6 + |x.1 - 1| * ‖x.2‖ ^ 4) := by
  have hd11 : 11 ≤ d := by omega
  have hnat := LocalEleven.UniformComplementBounds.physicalReducedEnergy_quartic_paper_native hd11
  have hb : (fun x : ℝ × Coordinates d => (LocalEleven.UniformComplementBounds.squaredAmplitude x.2) ^ 3 +
        |1 - 1 / x.1| * (LocalEleven.UniformComplementBounds.squaredAmplitude x.2) ^ 2)
      =O[𝓝 (1, (0 : Coordinates d))] (fun x => ‖x.2‖ ^ 6 + |x.1 - 1| * ‖x.2‖ ^ 4) := by
    refine IsBigO.of_bound ((d : ℝ) ^ 3 + 2 * (d : ℝ) ^ 2) ?_
    have ht : Tendsto (Prod.fst : ℝ × Coordinates d → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
      continuous_fst.continuousAt
    filter_upwards [ht.eventually delta_inv_le] with x hx
    have hS0 := LocalEleven.UniformComplementBounds.squaredAmplitude_nonneg x.2
    have hS := squaredAmplitude_le_card x.2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h3 : (LocalEleven.UniformComplementBounds.squaredAmplitude x.2) ^ 3 ≤
        (d : ℝ) ^ 3 * ‖x.2‖ ^ 6 := by
      calc _ ≤ ((d : ℝ) * ‖x.2‖ ^ 2) ^ 3 := pow_le_pow_left₀ hS0 hS 3
        _ = _ := by ring
    have h2 : (LocalEleven.UniformComplementBounds.squaredAmplitude x.2) ^ 2 ≤
        (d : ℝ) ^ 2 * ‖x.2‖ ^ 4 := by
      calc _ ≤ ((d : ℝ) * ‖x.2‖ ^ 2) ^ 2 := pow_le_pow_left₀ hS0 hS 2
        _ = _ := by ring
    have hm := mul_le_mul hx h2 (by positivity) (by positivity : 0 ≤ 2 * |x.1 - 1|)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hp1 : 0 ≤ ‖x.2‖ ^ 6 := by positivity
    have hp2 : 0 ≤ |x.1 - 1| * ‖x.2‖ ^ 4 := by positivity
    have hd3 : 0 ≤ (d : ℝ) ^ 3 := by positivity
    have hd2 : 0 ≤ (d : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hd2 hp2, mul_nonneg hd3 hp2, mul_nonneg hd2 hp1]
  refine (hnat.trans hb).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [physicalReducedEnergy_eq_core hd] with x hx
  rw [hx]
  rfl

#print axioms physicalReducedEnergy_joint_quartic_native

end BecknerOnofri.V2.Reaudit.SobolevQuartic
