import BecknerOnofri.ComplementParameterDifference

/-! The actual complement varies by O(|μ−1|‖z‖²), uniformly near the onset. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology
namespace BecknerOnofri.HighDim.UniformComplementBounds
open ContinuousGibbs ContinuousFirstShell ContinuousComplement GreenLocalBranch ReducedEquation
open ReducedCubicExpansion QuadraticSlaving

theorem correction_parameter_bound {d : ℕ} (hd : 12 ≤ d) :
    (fun x => correction hd x - correction hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))] (fun x => |x.1-1| *‖x.2‖^2) := by
  let B := uniformInverseBound d
  let L := nonlinearGreen d
  have hB : 0 < B := uniformInverseBound_pos d
  have hUpair : Tendsto (fun x => (potential hd x,potential hd (sliceMap d x)))
      (𝓝 (1,(0 : Coordinates d))) (𝓝 (0,0)) :=
    (potential_tendsto hd).prodMk_nhds ((potential_tendsto hd).comp (sliceMap_tendsto d))
  obtain ⟨C,hC,hLip⟩ := ((nonlinearRemainder_difference d).comp_tendsto hUpair).exists_pos
  have hm : Tendsto (fun x => max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖)
      (𝓝 (1,(0 : Coordinates d))) (𝓝 0) := by
    convert! (potential_tendsto hd).norm.max
      (((potential_tendsto hd).comp (sliceMap_tendsto d)).norm) using 1 <;>
      simp only [Function.comp_apply, norm_zero, max_self]
  have hsmall : ∀ᶠ x in 𝓝 (1,(0 : Coordinates d)),
      2*B*‖L‖*C*max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖ < 1/2 := by
    have ht := hm.const_mul (2*B*‖L‖*C)
    simp only [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  have hD : (fun x => correction hd x - correction hd (sliceMap d x))
      =O[𝓝 (1,(0 : Coordinates d))]
        (fun x => |x.1-1| *‖correction hd (sliceMap d x)‖) := by
    apply IsBigO.of_bound (2*B)
    filter_upwards [correction_solves hd, (sliceMap_tendsto d).eventually (correction_solves hd),
      parameter_interval (d := d), hLip.bound, hsmall] with x hx hs hμ hLipx hsmallx
    have h0 := correction_equation hd (sliceMap d x) hs
    simp only [show (sliceMap d x).1 = 1 from rfl, one_smul, sub_eq_zero] at h0
    have he := correction_difference_resolvent hd x hx hs hμ.1 hμ.2
    rw [← h0] at he
    have hLipx' : ‖nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x))‖ ≤
        C*(max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖ *
          ‖correction hd x - correction hd (sliceMap d x)‖) := by
      simpa only [Function.comp_apply, norm_mul, norm_norm,
        Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _)), potential_difference, Submodule.norm_coe] using hLipx
    have hmain : ‖correction hd x - correction hd (sliceMap d x)‖ ≤
        B*(|x.1-1| *‖correction hd (sliceMap d x)‖ +
          2*‖L‖*C*max ‖potential hd x‖ ‖potential hd (sliceMap d x)‖*
            ‖correction hd x - correction hd (sliceMap d x)‖) := by
      calc
        _ ≤ B*‖(x.1-1) • correction hd (sliceMap d x) +
            x.1 • L (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))‖ := by
          rw [he]
          exact continuousComplementInverse_norm_le hd hμ.1 hμ.2 _
        _ ≤ B*(‖(x.1-1) • correction hd (sliceMap d x)‖ +
            ‖x.1 • L (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x)))‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hB.le
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hB.le
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ.1]
          apply add_le_add le_rfl
          have hb := mul_le_mul hμ.2 (L.le_opNorm
            (nonlinearRemainder (potential hd x) - nonlinearRemainder (potential hd (sliceMap d x))))
            (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
          have hc := mul_le_mul_of_nonneg_left hLipx' (show (0:ℝ)≤2*‖L‖ by positivity)
          nlinarith
    have hh := mul_le_mul_of_nonneg_right hsmallx.le
      (norm_nonneg (correction hd x - correction hd (sliceMap d x)))
    simp only [norm_mul, norm_norm, Real.norm_eq_abs, abs_abs, abs_norm]
    nlinarith
  have hw := (correction_uniform_quadratic hd).comp_tendsto (sliceMap_tendsto d)
  have ha : (fun x : ℝ × Coordinates d => |x.1-1|) =O[𝓝 (1,0)] (fun x => |x.1-1|) := isBigO_refl _ _
  exact hD.trans (ha.mul hw.norm_left)

#print axioms correction_parameter_bound
end BecknerOnofri.HighDim.UniformComplementBounds
