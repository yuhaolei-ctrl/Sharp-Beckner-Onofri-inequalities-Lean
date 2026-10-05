module

public import Legacy.BecknerOnofri.JacobiHeatBounds

@[expose] public section

/-! Uniform convergence of all time-space derivatives and genuine joint C-infinity
smoothness of the complete normalized Jacobi heat series for positive time. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Legacy.BecknerOnofri.JacobiHeatBounds
open JacobiEigenfunctions

def openTimeSlab (ε : ℝ) : Set HeatSpace := {z | ε < z 0}

theorem openTimeSlab_isOpen (ε : ℝ) : IsOpen (openTimeSlab ε) :=
  isOpen_lt continuous_const (continuous_apply 0)

theorem openTimeSlab_convex (ε : ℝ) : Convex ℝ (openTimeSlab ε) :=
  (convex_Ioi ε).linear_preimage (ContinuousLinearMap.proj (0:Fin 3) : HeatSpace →L[ℝ] ℝ).toLinearMap

theorem closure_openTimeSlab_subset (ε : ℝ) : closure (openTimeSlab ε) ⊆ timeSlab ε := by
  apply closure_minimal _ (isClosed_le continuous_const (continuous_apply 0))
  intro z hz
  exact (show ε < z 0 from hz).le

theorem jointHeat_eq_heatKernel (m : ℕ) (z : HeatSpace) : jointHeat m z = heatKernel m (z 0) (z 1) (z 2) := by
  unfold jointHeat heatKernel
  apply tsum_congr
  intro n
  rw [heatTerm,Fin.prod_univ_three]
  simp only [heatFactor,ite_true,if_neg (show (1:Fin 3) ≠ 0 by decide),if_neg (show (2:Fin 3) ≠ 0 by decide)]
  rw [show -(eigenvalue m n)*z 0 = -(z 0)*eigenvalue m n by ring]

theorem heat_derivative_summable (m k : ℕ) {z : HeatSpace} (hz : 0 < z 0) :
    Summable (fun n : ℕ => iteratedFDeriv ℝ k (heatTerm m n) z) :=
  (heatMajorant_summable hz m k).of_norm_bounded (fun n => heatTerm_derivative_bound m n k (le_refl (z 0)))

theorem heat_derivative_series_uniform (m k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, iteratedFDeriv ℝ k (heatTerm m n) z)
      (fun z => ∑' n : ℕ, iteratedFDeriv ℝ k (heatTerm m n) z) atTop (timeSlab ε) :=
  tendstoUniformlyOn_tsum_nat (heatMajorant_summable hε m k)
    (fun n _ hz => heatTerm_derivative_bound m n k hz)

theorem jointHeat_contDiffOn_closure (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (jointHeat m) (closure (openTimeSlab ε)) :=
  ClosedConvexSmoothSeries.contDiffOn_tsum_closure (openTimeSlab_isOpen ε) (openTimeSlab_convex ε)
    (heatTerm_contDiff m) (fun k => heatMajorant_summable hε m k)
    (fun k n _ hz => heatTerm_derivative_bound m n k (closure_openTimeSlab_subset ε hz))

theorem jointHeat_contDiffAt (m : ℕ) {z : HeatSpace} (hz : 0 < z 0) : ContDiffAt ℝ ∞ (jointHeat m) z := by
  have hε : 0 < z 0/2 := by linarith
  have hm : z ∈ openTimeSlab (z 0/2) := by change z 0/2 < z 0; linarith
  exact (jointHeat_contDiffOn_closure m hε).contDiffAt
    (Filter.mem_of_superset ((openTimeSlab_isOpen _).mem_nhds hm) subset_closure)

theorem jointHeat_contDiffOn_slab (m : ℕ) {ε : ℝ} (hε : 0 < ε) : ContDiffOn ℝ ∞ (jointHeat m) (timeSlab ε) :=
  fun _ hz => (jointHeat_contDiffAt m (lt_of_lt_of_le hε hz)).contDiffWithinAt

theorem jointHeat_derivative_eq_series (m k : ℕ) {z : HeatSpace} (hz : 0 < z 0) :
    iteratedFDeriv ℝ k (jointHeat m) z = ∑' n : ℕ, iteratedFDeriv ℝ k (heatTerm m n) z := by
  induction k generalizing z with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ HeatSpace ℝ).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    let ε := z 0/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hzS : z ∈ openTimeSlab ε := by change z 0/2 < z 0; linarith
    have he : iteratedFDeriv ℝ k (jointHeat m) =ᶠ[𝓝 z]
        (fun w => ∑' n : ℕ, iteratedFDeriv ℝ k (heatTerm m n) w) := by
      filter_upwards [(openTimeSlab_isOpen ε).mem_nhds hzS] with w hw
      exact ih (hε.trans hw)
    have hfinite (n : ℕ) : ContDiff ℝ ((k+1:ℕ):ℕ∞ω) (heatTerm m n) :=
      (heatTerm_contDiff m n).of_le (by exact_mod_cast (le_top : ((k+1:ℕ):ℕ∞) ≤ ⊤))
    have hd (n : ℕ) : Differentiable ℝ (iteratedFDeriv ℝ k (heatTerm m n)) :=
      (hfinite n).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)
    have hsum := hasFDerivAt_tsum_of_isPreconnected (heatMajorant_summable hε m (k+1))
      (openTimeSlab_isOpen ε) (openTimeSlab_convex ε).isPreconnected
      (fun n w _ => (hd n w).hasFDerivAt)
      (fun n w hw => by
        rw [norm_fderiv_iteratedFDeriv]
        exact heatTerm_derivative_bound m n (k+1) (show ε ≤ w 0 from (show ε < w 0 from hw).le))
      hzS (heat_derivative_summable m k hz) hzS
    rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,he.fderiv_eq,hsum.fderiv]
    have hh :
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => HeatSpace) ℝ).symm
          (∑' n : ℕ, fderiv ℝ (iteratedFDeriv ℝ k (heatTerm m n)) z) =
        ∑' n : ℕ, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => HeatSpace) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ k (heatTerm m n)) z) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => HeatSpace) ℝ).symm.toContinuousLinearEquiv.map_tsum
    simpa only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply] using hh

theorem heat_derivatives_uniform (m k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, iteratedFDeriv ℝ k (heatTerm m n) z)
      (iteratedFDeriv ℝ k (jointHeat m)) atTop (timeSlab ε) := by
  apply (heat_derivative_series_uniform m k hε).congr_right
  intro z hz
  exact (jointHeat_derivative_eq_series m k (lt_of_lt_of_le hε hz)).symm

#print axioms jointHeat_contDiffAt
#print axioms jointHeat_derivative_eq_series
#print axioms heat_derivatives_uniform
end Legacy.BecknerOnofri.JacobiHeatBounds
