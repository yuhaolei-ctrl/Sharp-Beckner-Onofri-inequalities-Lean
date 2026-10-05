module

public import BecknerOnofri.GraphSobolevBounds
public import BecknerOnofri.GraphRegularity
public import BecknerOnofri.OnsetWienerBounds
public import BecknerOnofri.WeightedExponentialRemainder

@[expose] public section

/-! Quantitative polynomial Wiener bounds for the genuine complementary graph. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.GraphWienerBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open QuadraticModes GraphEnergy UniformComplementBounds GraphSobolevBounds GraphRegularity
open BecknerOnofri.OnsetWienerBounds
open Legacy.BecknerOnofri.RadialWiener Legacy.BecknerOnofri.WeightedWiener

abbrev wienerSize {d : ℕ} (m : ℕ) (u : Space d) : ℝ :=
  radialSize m (fun k => coefficient k u)

theorem correction_radial {d : ℕ} (hd : 0 < d) (μ : ℝ)
    (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (m : ℕ) : Radial m (w : Space d) := by
  apply radial_of_same_complement m _ _ (reconstruction_radial hd μ z w he m)
  intro k hk
  rw [reconstruction_apply, map_add]
  have hv : coefficient k (assembly d z) = 0 := by
    rw [← projection_assembly z]
    exact coefficient_projection_off_shell _ _ hk.2
  rw [hv, zero_add]

theorem continuousFourier_norm_le {d : ℕ} (u : Space d) : ‖continuousFourier d u‖ ≤ ‖u‖ := by
  change ‖Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d (toL2 d u)‖ ≤ ‖u‖
  rw [(Legacy.BecknerOnofri.TorusSobolev.fourierIsometry d).norm_map]
  simpa using (toL2 d).le_of_opNorm_le (toL2_norm_le d) u

theorem correction_coefficient_green_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (k : Frequency d) :
    ‖coefficient k (w : Space d)‖ ≤ 4*‖greenFourierVector d k *
      continuousFourier d (nonlinearRemainder (reconstruction d (z,w))) k‖ := by
  by_cases hk : ComplementFrequency k
  · have hlambda : 0 < frequencyLength k^d := lt_of_lt_of_le (by norm_num) (complement_eigenvalue_ge_sixtyfour hd hk)
    have hh := weighted_coefficient_bound hd hμ0 hμ2 z w he k
    rw [greenFourierVector_apply (by omega), if_neg hk.1, continuousFourier_apply,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (4*‖coefficient k (nonlinearRemainder (reconstruction d (z,w)))‖) / frequencyLength k^d :=
        (le_div_iff₀ hlambda).mpr (by simpa [mul_comm] using hh)
      _ = _ := by ring
  · rw [(mem_complement_fourier_iff (w : Space d)).mp w.property k hk, norm_zero]
    positivity

theorem correction_wiener_zero_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) :
    wienerSize 0 (w : Space d) ≤ (4*‖greenFourierVector d‖)*
      ‖nonlinearRemainder (reconstruction d (z,w))‖ := by
  let R := nonlinearRemainder (reconstruction d (z,w))
  have hs : Summable (fun k => ‖coefficient k (w : Space d)‖) :=
    (radialSummable_zero _).mp (correction_radial (by omega) μ z w he 0)
  calc
    _ = ∑' k, ‖coefficient k (w : Space d)‖ := by simp [wienerSize, radialSize, radialWeight]
    _ ≤ ∑' k, 4*‖greenFourierVector d k * continuousFourier d R k‖ :=
      hs.tsum_le_tsum (correction_coefficient_green_bound hd hμ0 hμ2 z w he)
        ((green_series_summable d (continuousFourier d R)).mul_left 4)
    _ = 4 * ∑' k, ‖greenFourierVector d k‖ * ‖continuousFourier d R k‖ := by
      rw [tsum_mul_left]
      simp only [norm_mul]
    _ ≤ 4*(‖greenFourierVector d‖*‖continuousFourier d R‖) :=
      mul_le_mul_of_nonneg_left (lp.tsum_mul_le_mul_norm'
        (by simpa using Real.HolderConjugate.two_two) (greenFourierVector d) (continuousFourier d R)) (by norm_num)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (continuousFourier_norm_le R) (norm_nonneg (greenFourierVector d))]

theorem correction_wiener_step_bound {d : ℕ} (hd : 12 ≤ d) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ2 : μ ≤ 2) (z : Coordinates d) (w : complement d)
    (he : projectedEquation (greenContinuous d) ((μ,z),w) = 0) (m : ℕ)
    (hR : Radial m (nonlinearRemainder (reconstruction d (z,w)))) :
    wienerSize (m+d) (w : Space d) ≤ (4*2^d)*
      wienerSize m (nonlinearRemainder (reconstruction d (z,w))) := by
  unfold wienerSize radialSize
  rw [← tsum_mul_left]
  apply (correction_radial (by omega) μ z w he (m+d)).tsum_le_tsum _ (hR.mul_left _)
  intro k
  dsimp only
  by_cases hk : ComplementFrequency k
  · have hr := Legacy.BecknerOnofri.TorusSobolev.radius_one_le hk.1
    have hh := weighted_coefficient_bound hd hμ0 hμ2 z w he k
    rw [Bridge.frequencyLength_eq] at hh
    have hp : (1+Legacy.TorusEndpoint.frequencyRadius k)^d ≤
        2^d*Legacy.TorusEndpoint.frequencyRadius k^d := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) d
    change (1+Legacy.TorusEndpoint.frequencyRadius k)^(m+d)*‖coefficient k (w : Space d)‖ ≤ _
    rw [pow_add]
    have hm := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (1+Legacy.TorusEndpoint.frequencyRadius k)^m from by positivity)
    have hp' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (show 0 ≤ (1+Legacy.TorusEndpoint.frequencyRadius k)^m from by positivity))
      (norm_nonneg (coefficient k (w : Space d)))
    simp only [radialWeight]
    simp only [reconstruction_apply] at hh hm ⊢
    nlinarith [mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 2^d by positivity)]
  · rw [(mem_complement_fourier_iff (w : Space d)).mp w.property k hk, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _))

theorem radial_add {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    Radial m (u+v) := by
  apply (hu.add hv).of_nonneg_of_le
  · intro k
    exact mul_nonneg ((radialWeight_isWeight m).nonneg k) (norm_nonneg _)
  · intro k
    dsimp only
    rw [map_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ((radialWeight_isWeight m).nonneg k)

theorem wienerSize_add_le {d : ℕ} (m : ℕ) (u v : Space d) (hu : Radial m u) (hv : Radial m v) :
    wienerSize m (u+v) ≤ wienerSize m u+wienerSize m v := by
  unfold wienerSize radialSize
  rw [← hu.tsum_add hv]
  apply (radial_add m u v hu hv).tsum_le_tsum _ (hu.add hv)
  intro k
  dsimp only
  rw [map_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) ((radialWeight_isWeight m).nonneg k)

theorem radial_zero {d : ℕ} (m : ℕ) : Radial m (0 : Space d) := by
  simp [Radial, RadialSummable]

theorem radial_synthesis {d : ℕ} (m : ℕ) (k : Frequency d) (z : ℂ) : Radial m (synthesis k z) := by
  classical
  have hs := ((hasSum_ite_eq k (radialWeight m k*‖z‖)).add
    (hasSum_ite_eq (-k) (radialWeight m k*‖z‖))).summable
  apply hs.of_nonneg_of_le
  · intro j
    exact mul_nonneg ((radialWeight_isWeight m).nonneg j) (norm_nonneg _)
  · intro j
    dsimp only
    rw [coefficient_synthesis]
    calc
      _ ≤ radialWeight m j * (‖if j=k then z else 0‖+‖if j= -k then star z else 0‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) ((radialWeight_isWeight m).nonneg j)
      _ = _ := by
        by_cases hj : j=k <;> by_cases hj' : j= -k <;>
          simp_all [radialWeight, Legacy.TorusEndpoint.frequencyRadius_neg, mul_add]

theorem wienerSize_synthesis_le {d : ℕ} (m : ℕ) (k : Frequency d) (z : ℂ) :
    wienerSize m (synthesis k z) ≤ 2*radialWeight m k*‖z‖ := by
  classical
  have hs := (hasSum_ite_eq k (radialWeight m k*‖z‖)).add
    (hasSum_ite_eq (-k) (radialWeight m k*‖z‖))
  have hb := hasSum_le (fun j => ?_) (radial_synthesis m k z).hasSum hs
  · simpa only [wienerSize, radialSize, two_mul, add_mul] using hb
  · dsimp only
    rw [coefficient_synthesis]
    calc
      _ ≤ radialWeight m j * (‖if j=k then z else 0‖+‖if j= -k then star z else 0‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) ((radialWeight_isWeight m).nonneg j)
      _ = _ := by
        by_cases hj : j=k <;> by_cases hj' : j= -k <;>
          simp_all [radialWeight, Legacy.TorusEndpoint.frequencyRadius_neg, mul_add]

theorem radial_finset_sum {d : ℕ} {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → Space d)
    (hf : ∀ i∈s, Radial m (f i)) : Radial m (∑ i∈s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using radial_zero (d := d) m
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact radial_add m _ _ (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem wienerSize_finset_sum_le {d : ℕ} {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → Space d)
    (hf : ∀ i∈s, Radial m (f i)) : wienerSize m (∑ i∈s, f i) ≤ ∑ i∈s,wienerSize m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wienerSize, radialSize]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : ∀ j∈s, Radial m (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    exact (wienerSize_add_le m _ _ (hf i (Finset.mem_insert_self _ _))
      (radial_finset_sum m s f hs)).trans (add_le_add le_rfl (ih hs))

theorem radial_assembly {d : ℕ} (m : ℕ) (z : Coordinates d) : Radial m (assembly d z) := by
  rw [assembly_apply]
  exact radial_finset_sum m _ _ (fun i _ => radial_synthesis m _ _)

theorem wienerSize_assembly_le {d : ℕ} (m : ℕ) (z : Coordinates d) :
    wienerSize m (assembly d z) ≤ (2^(m+1)*d)*‖z‖ := by
  rw [assembly_apply]
  calc
    _ ≤ ∑ i, wienerSize m (synthesis (axisFrequency i) (z i)) :=
      wienerSize_finset_sum_le m _ _ (fun i _ => radial_synthesis m _ _)
    _ ≤ ∑ i : Fin d, 2^(m+1)*‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ 2*radialWeight m (axisFrequency i)*‖z i‖ := wienerSize_synthesis_le m _ _
        _ = 2^(m+1)*‖z i‖ := by rw [radialWeight, frequencyRadius_axisFrequency]; norm_num only [one_add_one_eq_two]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (by positivity)
    _ = _ := by simp [mul_assoc, mul_comm]

theorem correction_wiener_zero_quadratic {d : ℕ} (hd : 12 ≤ d) :
    (fun x => wienerSize 0 (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  have hR : (fun x => nonlinearRemainder (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) :=
    ((nonlinearRemainder_quadratic d).comp_tendsto (UniformComplementBounds.potential_tendsto hd)).trans
      ((potential_uniform_linear hd).norm_left.pow 2)
  have hb : (fun x => wienerSize 0 (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => nonlinearRemainder (potential hd x)) := by
    apply IsBigO.of_bound (4*‖greenFourierVector d‖)
    filter_upwards [correction_solves hd, parameter_interval (d := d)] with x hx hμ
    rw [Real.norm_eq_abs, abs_of_nonneg (radialSize_nonneg _ _)]
    exact correction_wiener_zero_bound hd hμ.1 hμ.2 x.2 (correction hd x) hx
  exact hb.trans hR

theorem potential_wiener_linear_of_correction {d : ℕ} (hd : 12 ≤ d) (m : ℕ)
    (hw : (fun x => wienerSize m (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2)) :
    (fun x => wienerSize m (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖) := by
  have hv : (fun x : ℝ × Coordinates d => wienerSize m (assembly d x.2))
      =O[𝓝 (1,0)] (fun x => ‖x.2‖) := by
    apply IsBigO.of_bound (2^(m+1)*d)
    exact Eventually.of_forall (fun x => by
      simpa only [Real.norm_of_nonneg (radialSize_nonneg _ _), norm_norm] using wienerSize_assembly_le m x.2)
  have ht : Tendsto (Prod.snd : ℝ × Coordinates d → Coordinates d) (𝓝 (1,0)) (𝓝 0) :=
    continuous_snd.continuousAt
  have hw1 := hw.trans (QuadraticSlaving.pow_down.comp_tendsto ht)
  have hb : (fun x => wienerSize m (potential hd x)) =O[𝓝 (1,(0 : Coordinates d))]
      (fun x => wienerSize m (assembly d x.2) + wienerSize m (correction hd x : Space d)) := by
    apply IsBigO.of_bound 1
    filter_upwards [correction_solves hd] with x hx
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _), Real.norm_of_nonneg
      (add_nonneg (radialSize_nonneg _ _) (radialSize_nonneg _ _)), one_mul]
    exact wienerSize_add_le m _ _ (radial_assembly m x.2)
      (correction_radial (by omega) x.1 x.2 (correction hd x) hx m)
  exact hb.trans (hv.add hw1)

theorem nonlinear_wiener_quadratic_of_potential {d : ℕ} (hd : 12 ≤ d) (m : ℕ)
    (hu : (fun x => wienerSize m (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖)) :
    (fun x => wienerSize m (nonlinearRemainder (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  have ht : Tendsto (fun x : ℝ × Coordinates d => ‖x.2‖) (𝓝 (1,0)) (𝓝 0) := by
    simpa using (continuous_snd.continuousAt (x := (1,(0 : Coordinates d)))).norm.tendsto
  have hsmall := (hu.trans_tendsto ht).eventually_le_const (by norm_num : (0:ℝ)<1)
  have hb : (fun x => wienerSize m (nonlinearRemainder (potential hd x)))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => (wienerSize m (potential hd x))^2) := by
    apply IsBigO.of_bound (9/4)
    filter_upwards [correction_solves hd, hsmall] with x hx hs
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _), Real.norm_of_nonneg (sq_nonneg _)]
    exact WeightedExponentialRemainder.nonlinear_radialSize_le_quadratic m _
      (reconstruction_radial (by omega) x.1 x.2 (correction hd x) hx m)
      (mean_reconstruction _) hs
  exact hb.trans (hu.pow 2)

theorem correction_wiener_step_quadratic {d : ℕ} (hd : 12 ≤ d) (m : ℕ)
    (hw : (fun x => wienerSize m (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2)) :
    (fun x => wienerSize (m+d) (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  have hR := nonlinear_wiener_quadratic_of_potential hd m (potential_wiener_linear_of_correction hd m hw)
  have hb : (fun x => wienerSize (m+d) (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => wienerSize m (nonlinearRemainder (potential hd x))) := by
    apply IsBigO.of_bound (4*2^d)
    filter_upwards [correction_solves hd, parameter_interval (d := d)] with x hx hμ
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _), Real.norm_of_nonneg (radialSize_nonneg _ _)]
    exact correction_wiener_step_bound hd hμ.1 hμ.2 x.2 (correction hd x) hx m
      (WeightedExponentialRemainder.nonlinear_radial m _
        (reconstruction_radial (by omega) x.1 x.2 (correction hd x) hx m))
  exact hb.trans hR

theorem wienerSize_mono {d : ℕ} {m n : ℕ} (hmn : m≤n) (u : Space d) (hu : Radial n u) :
    wienerSize m u ≤ wienerSize n u := by
  apply (radialSummable_mono hmn hu).tsum_le_tsum _ hu
  intro k
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact pow_le_pow_right₀ (by
    have := Legacy.TorusEndpoint.frequencyRadius_nonneg k
    change (1:ℝ) ≤ 1+Legacy.TorusEndpoint.frequencyRadius k
    linarith) hmn

/-- The correction is uniformly quadratic in every polynomial Wiener norm. -/
theorem correction_wiener_quadratic {d : ℕ} (hd : 12 ≤ d) (m : ℕ) :
    (fun x => wienerSize m (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
  have hmultiple (n : ℕ) : (fun x => wienerSize (n*d) (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖^2) := by
    induction n with
    | zero => simpa using correction_wiener_zero_quadratic hd
    | succ n ih => simpa only [Nat.succ_mul] using correction_wiener_step_quadratic hd (n*d) ih
  have hb : (fun x => wienerSize m (correction hd x : Space d))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => wienerSize (m*d) (correction hd x : Space d)) := by
    apply IsBigO.of_bound 1
    filter_upwards [correction_solves hd] with x hx
    rw [Real.norm_of_nonneg (radialSize_nonneg _ _), Real.norm_of_nonneg (radialSize_nonneg _ _), one_mul]
    exact wienerSize_mono (Nat.le_mul_of_pos_right m (by omega)) _
      (correction_radial (by omega) x.1 x.2 (correction hd x) hx (m*d))
  exact hb.trans (hmultiple m)

theorem potential_wiener_linear {d : ℕ} (hd : 12 ≤ d) (m : ℕ) :
    (fun x => wienerSize m (potential hd x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => ‖x.2‖) :=
  potential_wiener_linear_of_correction hd m (correction_wiener_quadratic hd m)

#print axioms correction_wiener_zero_bound
#print axioms correction_wiener_step_bound
#print axioms correction_wiener_quadratic
#print axioms potential_wiener_linear
end BecknerOnofri.HighDim.GraphWienerBounds
