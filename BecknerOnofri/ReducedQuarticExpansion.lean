module

public import BecknerOnofri.SlavedGibbs

@[expose] public section

/-! The actual graph expression for the critical reduced pressure has the
manuscript's exact quartic coefficients, with a controlled fifth-order remainder.
The equality with the physical energy functional is proved separately. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.ReducedQuarticExpansion
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving SlavedMoments

/-- Actual logarithmic/Gibbs expression on the solved complementary graph. -/
def graphExpression {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) : ℝ :=
  centeredLogPartition (U hd z) - mean d (V d z^2)/2 -
    mean d (W hd z * normalized (U hd z))/2

def quarticValue {d : ℕ} (z : Coordinates d) : ℝ :=
  quarticA d * (∑ i, ‖z i‖^4) + quarticB d * mixedAmplitudeSum z

theorem graphExpression_error {d : ℕ} (hd : 12 ≤ d) :
    (fun z => graphExpression hd z - (mean d (V d z^4)/24 - (mean d (V d z^2))^2/8 +
      mean d (V d z^2 * W hd z)/4))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  apply ((log_graph_error hd).sub ((W_normalized_error hd).const_mul_left (1/2:ℝ))).congr_left
  intro z
  unfold graphExpression
  rw [mul_comm (W hd z) (V d z^2)]
  ring

theorem pairing_quadraticCorrection {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    mean d (V d z^2 * (quadraticCorrection hd z : Space d))/4 =
      (1/8:ℝ)*pairing (quadraticSource z).val (resolvent hd (quadraticSource z)).val := by
  have hsource : (quadraticSource z).val = center d (V d z^2) := by
    rw [quadraticSource_value]
    rfl
  rw [quadraticCorrection_eq_resolvent]
  simp only [Submodule.coe_smul, mul_smul_comm, map_smul, smul_eq_mul, pairing_apply, hsource]
  rw [mul_comm (center d _) _, mean_mul_center _ _ ((resolvent hd (quadraticSource z)).property.1),
    mul_comm (V d z^2) _]
  ring

theorem pairing_remainder_order_five {d : ℕ} (hd : 12 ≤ d) :
    (fun z => mean d (V d z^2 * W hd z) -
      mean d (V d z^2 * (quadraticCorrection hd z : Space d)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have hw : (fun z => W hd z - (quadraticCorrection hd z : Space d))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) :=
    ((complement d).subtypeL.isBigO_comp _ _).trans (correction_quadratic_expansion hd)
  have hm : (fun z => V d z^2 * (W hd z - (quadraticCorrection hd z : Space d)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! (V_order.pow 2).mul hw using 1 <;> (ext z; ring)
  apply (((mean d).isBigO_comp _ _).trans hm).congr_left
  intro z
  rw [mul_sub, map_sub]

/-- Exact quartic coefficients in the genuine nonlinear graph expression. -/
theorem graphExpression_quartic {d : ℕ} (hd : 12 ≤ d) :
    (fun z => graphExpression hd z - quarticValue z)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  apply ((graphExpression_error hd).add
    ((pairing_remainder_order_five hd).const_mul_left (1/4:ℝ))).congr_left
  intro z
  have hq := actual_quartic_coefficients hd z
  rw [← pairing_quadraticCorrection hd z] at hq
  change _ = quarticValue z at hq
  rw [← hq]
  ring

#print axioms graphExpression_quartic
end BecknerOnofri.HighDim.ReducedQuarticExpansion
