import Legacy.BecknerOnofri.CountableCosineMixture
import Legacy.BecknerOnofri.UniformDensityLimits

/-! Strictly positive finite normalized mixtures approximating an actual
countable mixture with summable uniform majorant. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.CosineMixtureApproximation
open CosineMixture
variable {d : ℕ}

def epsilon (m : ℕ) : ℝ := 1/((m:ℝ)+2)
def remaining (w : ℕ → ℝ) (m : ℕ) : ℝ := 1 - ∑ n ∈ Finset.range m, w n
def partialSum (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (m : ℕ) (x : Torus d) : ℝ :=
  mixture (Finset.range m) w N x

def approx (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (m : ℕ) (x : Torus d) : ℝ :=
  (1-epsilon m)*(partialSum w N m x + remaining w m) + epsilon m

def finiteWeight (w : ℕ → ℝ) (m n : ℕ) : ℝ :=
  if n < m then (1-epsilon m)*w n else (1-epsilon m)*remaining w m+epsilon m

def finiteIndex (N : ℕ → Fin d → ℕ) (m n : ℕ) : Fin d → ℕ :=
  if n < m then N n else fun _ => 0

theorem epsilon_pos (m : ℕ) : 0 < epsilon m := by unfold epsilon; positivity

theorem epsilon_le_one (m : ℕ) : epsilon m ≤ 1 := by
  unfold epsilon
  apply (div_le_one (by positivity : (0:ℝ) < m+2)).2
  have h : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem epsilon_tendsto : Tendsto epsilon atTop (𝓝 0) := by
  have h := (tendsto_add_atTop_iff_nat 2).2
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

theorem remaining_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) :
    0 ≤ remaining w m := by
  have h := hm.summable.sum_le_tsum (Finset.range m) (fun n _ => hw n)
  rw [hm.tsum_eq] at h
  exact sub_nonneg.mpr h

theorem remaining_le_one (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (m : ℕ) :
    remaining w m ≤ 1 := by
  have h : 0 ≤ ∑ n ∈ Finset.range m, w n := Finset.sum_nonneg (fun n _ => hw n)
  unfold remaining
  linarith

theorem remaining_tendsto (w : ℕ → ℝ) (hm : HasSum w 1) :
    Tendsto (remaining w) atTop (𝓝 0) := by
  have h : Tendsto (fun m => (1:ℝ) - ∑ n ∈ Finset.range m, w n)
      atTop (𝓝 (1-1)) := tendsto_const_nhds.sub hm.tendsto_sum_nat
  change Tendsto (fun m => (1:ℝ) - ∑ n ∈ Finset.range m, w n) atTop (𝓝 0)
  simpa only [sub_self] using h

theorem partial_nonneg (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (m : ℕ) (x : Torus d) : 0 ≤ partialSum w N m x :=
  mixture_nonneg _ _ _ (fun n _ => hw n) x

theorem partial_le_majorant (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hSup : Summable (fun n => w n * tensor (N n) 0)) (m : ℕ) (x : Torus d) :
    partialSum w N m x ≤ majorant w N := by
  apply le_trans ((summable_terms w N hw hSup x).sum_le_tsum (Finset.range m)
    (fun n _ => mul_nonneg (hw n) (tensor_nonneg _ _)))
  exact rho_le_majorant w N hw hSup x

theorem finiteWeight_nonneg (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (m n : ℕ) : 0 ≤ finiteWeight w m n := by
  unfold finiteWeight
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr (epsilon_le_one m)) (hw n)
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr (epsilon_le_one m))
      (remaining_nonneg w hw hm m)) (epsilon_pos m).le

theorem finiteWeight_mass (w : ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range (m+1), finiteWeight w m n = 1 := by
  rw [Finset.sum_range_succ]
  have h : (∑ n ∈ Finset.range m, finiteWeight w m n) =
      (1-epsilon m) * ∑ n ∈ Finset.range m, w n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp [finiteWeight, Finset.mem_range.mp hn]
  rw [h]
  simp only [finiteWeight, lt_self_iff_false, ↓reduceIte]
  unfold remaining
  ring

/-- The displayed approximation really is a finite correlated cosine mixture. -/
theorem finite_mixture_eq_approx (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (m : ℕ) (x : Torus d) :
    mixture (Finset.range (m+1)) (finiteWeight w m) (finiteIndex N m) x = approx w N m x := by
  unfold mixture
  rw [Finset.sum_range_succ]
  have h : (∑ n ∈ Finset.range m, finiteWeight w m n * tensor (finiteIndex N m n) x) =
      (1-epsilon m) * ∑ n ∈ Finset.range m, w n * tensor (N n) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp [finiteWeight, finiteIndex, Finset.mem_range.mp hn, mul_assoc]
  rw [h]
  simp only [finiteWeight, finiteIndex, lt_self_iff_false, ↓reduceIte, tensor_zero_index, mul_one]
  unfold approx partialSum mixture
  ring

def approximatingDensity (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) : ProbabilityDensity d :=
  density (Finset.range (m+1)) (finiteWeight w m) (finiteIndex N m)
    (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)

theorem approximatingDensity_value (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) :
    (approximatingDensity w N hw hm m).value = approx w N m :=
  funext (finite_mixture_eq_approx w N m)

theorem approx_continuous (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (m : ℕ) :
    Continuous (approx w N m) := by
  exact (((mixture_continuous (Finset.range m) w N).add continuous_const).const_mul _).add
    continuous_const

theorem approx_pos (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (m : ℕ) (x : Torus d) : 0 < approx w N m x := by
  have h := mul_nonneg (sub_nonneg.mpr (epsilon_le_one m))
    (add_nonneg (partial_nonneg w N hw m x) (remaining_nonneg w hw hm m))
  exact add_pos_of_nonneg_of_pos h (epsilon_pos m)

theorem approx_le_majorant (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0))
    (m : ℕ) (x : Torus d) : approx w N m x ≤ majorant w N + 2 := by
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (partial_le_majorant w N hw hSup m x) (remaining_le_one w hw m))
    (sub_nonneg.mpr (epsilon_le_one m))
  have hp := mul_nonneg (epsilon_pos m).le (majorant_nonneg w N hw)
  unfold approx
  nlinarith

theorem approx_sub_partial_bound (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0))
    (m : ℕ) (x : Torus d) :
    ‖approx w N m x - partialSum w N m x‖ ≤
      remaining w m + epsilon m * (majorant w N + 2) := by
  rw [Real.norm_eq_abs, abs_le]
  have hT0 := partial_nonneg w N hw m x
  have hT := partial_le_majorant w N hw hSup m x
  have hr0 := remaining_nonneg w hw hm m
  have hr := remaining_le_one w hw m
  have he := epsilon_pos m
  have heT := mul_le_mul_of_nonneg_left hT he.le
  have heT0 := mul_nonneg he.le hT0
  have her := mul_le_mul_of_nonneg_left hr he.le
  have her0 := mul_nonneg he.le hr0
  have heM := mul_nonneg he.le (majorant_nonneg w N hw)
  unfold approx
  constructor <;> nlinarith

theorem approx_uniform (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    TendstoUniformly (approx w N) (rho w N) atTop := by
  have he : Tendsto (fun m => remaining w m + epsilon m * (majorant w N + 2))
      atTop (𝓝 0) := by
    simpa using (remaining_tendsto w hm).add (epsilon_tendsto.mul_const (majorant w N + 2))
  have hp := partial_uniform w N hw hSup
  apply Metric.tendstoUniformly_iff.mpr
  intro e he0
  have hpe := Metric.tendstoUniformly_iff.mp hp (e/2) (by linarith)
  have hee := (tendsto_order.1 he).2 (e/2) (by linarith)
  filter_upwards [hpe, hee] with m hpm hem
  intro x
  have hdist : dist (partialSum w N m x) (approx w N m x) ≤
      remaining w m + epsilon m * (majorant w N+2) := by
    rw [dist_comm, dist_eq_norm]
    exact approx_sub_partial_bound w N hw hm hSup m x
  have htri := dist_triangle (rho w N x) (partialSum w N m x) (approx w N m x)
  have hpart : dist (rho w N x) (partialSum w N m x) < e/2 := hpm x
  linarith

theorem approx_L1_tendsto (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    Tendsto (fun m => ∫ x, ‖approx w N m x - rho w N x‖ ∂torusMeasure d)
      atTop (𝓝 0) := by
  apply UniformDensityLimits.L1_tendsto_of_uniform (approx w N) (rho w N)
    (approx_continuous w N) (rho_continuous w N hw hSup) (majorant w N+2)
  · intro m x
    rw [Real.norm_of_nonneg (approx_pos w N hw hm m x).le]
    exact approx_le_majorant w N hw hm hSup m x
  · exact approx_uniform w N hw hm hSup

theorem approx_entropy_tendsto (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    Tendsto (fun m => densityEntropy (approx w N m))
      atTop (𝓝 (densityEntropy (rho w N))) := by
  apply UniformDensityLimits.entropy_tendsto_of_uniform (approx w N) (rho w N)
    (approx_continuous w N) (majorant w N+2)
  · intro m x
    rw [Real.norm_of_nonneg (approx_pos w N hw hm m x).le]
    exact approx_le_majorant w N hw hm hSup m x
  · exact approx_uniform w N hw hm hSup

theorem approximatingDensity_pos (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) (x : Torus d) :
    0 < (approximatingDensity w N hw hm m).value x := by
  rw [approximatingDensity_value]
  exact approx_pos w N hw hm m x

theorem approximatingDensity_finiteEntropy (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ)
    (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1) (m : ℕ) :
    (approximatingDensity w N hw hm m).FiniteEntropy :=
  CosineMixture.finiteEntropy _ _ _ _ _

theorem density_L1_tendsto (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    Tendsto (fun m => ∫ x, ‖(approximatingDensity w N hw hm m).value x -
      (probabilityDensity w N hw hm hSup).value x‖ ∂torusMeasure d) atTop (𝓝 0) := by
  simp_rw [approximatingDensity_value]
  exact approx_L1_tendsto w N hw hm hSup

theorem density_entropy_tendsto (w : ℕ → ℝ) (N : ℕ → Fin d → ℕ) (hw : ∀ n, 0 ≤ w n)
    (hm : HasSum w 1) (hSup : Summable (fun n => w n * tensor (N n) 0)) :
    Tendsto (fun m => densityEntropy (approximatingDensity w N hw hm m).value)
      atTop (𝓝 (densityEntropy (probabilityDensity w N hw hm hSup).value)) := by
  simp_rw [approximatingDensity_value]
  exact approx_entropy_tendsto w N hw hm hSup

#print axioms density_L1_tendsto
#print axioms density_entropy_tendsto
#print axioms finite_mixture_eq_approx
#print axioms approx_pos
#print axioms approx_uniform
end Legacy.BecknerOnofri.CosineMixtureApproximation
