import BecknerOnofri.SlavedMoments

/-! Controlled Gibbs pairings and logarithmic moments on the actual graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.SlavedMoments
open ContinuousGibbs ContinuousFirstShell QuadraticModes QuadraticSlaving

theorem mean_mul_center {d : ℕ} (w f : Space d) (hw : mean d w = 0) :
    mean d (w * center d f) = mean d (w*f) := by
  have he : w * center d f = w*f - mean d f • w := by
    ext x
    simp [center_apply]
    ring
  rw [he, map_sub, map_smul, hw, smul_zero, sub_zero]

theorem U_second_square_error {d : ℕ} (hd : 12 ≤ d) :
    (fun z => (mean d (U hd z^2))^2 - (mean d (V d z^2))^2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have hw : (fun z => W hd z^2) =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    convert! (W_order_two hd).mul (W_order_one hd) using 1 <;> (ext z; ring)
  have hu := ((mean d).isBigO_comp _ _).trans ((U_order hd).pow 2)
  have hv := ((mean d).isBigO_comp _ _).trans (V_order.pow 2)
  have hh : (fun z => mean d (W hd z^2) * (mean d (U hd z^2)+mean d (V d z^2)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! (((mean d).isBigO_comp _ _).trans hw).mul (hu.add hv) using 1 <;> (ext z; ring)
  apply hh.congr_left
  intro z
  rw [U_second]
  ring

theorem W_quadraticPolynomial_mean {d : ℕ} (hd : 12 ≤ d) (z : Coordinates d) :
    mean d (W hd z * quadraticPolynomial (U hd z)) =
      mean d (W hd z^2) + (1/2:ℝ)*mean d (W hd z * U hd z^2) := by
  have hc : center d (U hd z) = U hd z := ContinuousComplement.center_reconstruction _
  rw [quadraticPolynomial, quadraticTerm_of_mean_zero (mean_slicePotential hd z), hc,
    mul_add, mul_add, mul_one, mul_smul_comm, map_add, map_add, map_smul,
    mean_mul_center _ _ (W_mean hd z), W_mean, zero_add]
  have hh : mean d (W hd z * U hd z) = mean d (W hd z^2) := by
    rw [U_eq, mul_add, map_add, mean_mul_assembly, zero_add, pow_two]
  rw [hh]
  rfl

theorem W_normalized_error {d : ℕ} (hd : 12 ≤ d) :
    (fun z => mean d (W hd z * normalized (U hd z)) - mean d (W hd z^2) -
      (1/2:ℝ)*mean d (W hd z * V d z^2))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have hmain : (fun z => W hd z * (normalized (U hd z) - quadraticPolynomial (U hd z)))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! (W_order_two hd).mul (normalized_error_cubic hd) using 1 <;> (ext z; ring)
  have hs : (fun z => U hd z^2 - V d z^2)
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
    have hh : (fun z => W hd z * (U hd z+V d z))
        =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^3) := by
      convert! (W_order_two hd).mul ((U_order hd).add V_order) using 1 <;> (ext z; ring)
    apply hh.congr_left
    intro z
    rw [U_eq]
    ring
  have herr : (fun z => W hd z * (U hd z^2-V d z^2))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
    convert! (W_order_two hd).mul hs using 1 <;> (ext z; ring)
  have hm := ((mean d).isBigO_comp _ _).trans hmain
  have he := (((mean d).isBigO_comp _ _).trans herr).const_mul_left (1/2:ℝ)
  apply (hm.add he).congr_left
  intro z
  simp only [mul_sub, map_sub, W_quadraticPolynomial_mean]
  ring

/-- Expansion of the actual logarithmic partition on the complementary graph. -/
theorem log_graph_error {d : ℕ} (hd : 12 ≤ d) :
    (fun z => centeredLogPartition (U hd z) -
      (mean d (V d z^2)/2 + mean d (W hd z^2)/2 +
        mean d (V d z^2*W hd z)/2 + mean d (V d z^4)/24 - (mean d (V d z^2))^2/8))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) := by
  have hl : (fun z => centeredLogPartition (U hd z) - quarticLogPolynomial (U hd z))
      =O[𝓝 (0 : Coordinates d)] (fun z => ‖z‖^5) :=
    ((centeredLogPartition_quartic_remainder d).comp_tendsto (slicePotential_tendsto hd)).trans
      ((U_order hd).norm_left.pow 5)
  have h3 := (U_third_error hd).const_mul_left (1/6:ℝ)
  have h4 := (U_fourth_error hd).const_mul_left (1/24:ℝ)
  have h2 := (U_second_square_error hd).const_mul_left (1/8:ℝ)
  apply (((hl.add h3).add h4).sub h2).congr_left
  intro z
  have hc : center d (U hd z) = U hd z := ContinuousComplement.center_reconstruction _
  simp only [quarticLogPolynomial, centeredMoment, hc, U_second]
  ring

#print axioms W_normalized_error
#print axioms log_graph_error
end BecknerOnofri.HighDim.SlavedMoments
