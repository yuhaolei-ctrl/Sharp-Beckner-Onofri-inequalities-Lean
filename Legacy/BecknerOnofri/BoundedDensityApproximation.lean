import Legacy.BecknerOnofri.EndpointClosure

/-! Genuine bounded normalized truncations of any probability density.
Their pointwise convergence and common integrable domination require no
entropy or L2 hypothesis on the original density. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint Filter
open scoped Topology
namespace Legacy.BecknerOnofri.BoundedDensityApproximation

def cut {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) (x : Torus d) : ℝ :=
  min (max (r.value x) 0) ((n:ℝ)+1)

theorem cut_nonnegative {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) (x : Torus d) :
    0 ≤ cut r n x := le_min (le_max_right _ _) (by positivity)

theorem cut_measurable {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    AEStronglyMeasurable (cut r n) (torusMeasure d) :=
  ((r.integrable.aestronglyMeasurable.aemeasurable.max aemeasurable_const).min
    aemeasurable_const).aestronglyMeasurable

theorem cut_memLp {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    MemLp (cut r n) 2 (torusMeasure d) := by
  apply MemLp.of_bound (cut_measurable r n) ((n:ℝ)+1)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_of_nonneg (cut_nonnegative r n x)]
    exact min_le_right _ _)

theorem cut_integrable {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    Integrable (cut r n) (torusMeasure d) := (cut_memLp r n).integrable (by norm_num)

theorem cut_le {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    ∀ᵐ x ∂torusMeasure d, cut r n x ≤ r.value x := by
  filter_upwards [r.nonneg] with x hx
  exact (min_le_left _ _).trans_eq (max_eq_left hx)

def mass {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) : ℝ := ∫ x, cut r n x ∂torusMeasure d

theorem mass_pos {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) : 0 < mass r n := by
  apply lt_of_le_of_ne (integral_nonneg (cut_nonnegative r n))
  intro hz
  have hcut := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (cut_nonnegative r n))
    (cut_integrable r n)).mp hz.symm
  have hr : r.value =ᵐ[torusMeasure d] fun _ => 0 := by
    filter_upwards [hcut, r.nonneg] with x hx hn
    change min (max (r.value x) 0) ((n:ℝ)+1) = 0 at hx
    rw [max_eq_left hn] at hx
    have hcap : (0:ℝ) < (n:ℝ)+1 := by positivity
    by_contra he
    exact (ne_of_gt (lt_min (lt_of_le_of_ne hn (Ne.symm he)) hcap)) hx
  have hh := integral_congr_ae hr
  rw [r.mass, integral_zero] at hh
  norm_num at hh

theorem mass_le_one {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) : mass r n ≤ 1 := by
  exact (integral_mono_ae (cut_integrable r n) r.integrable (cut_le r n)).trans_eq r.mass

theorem mass_mono {d : ℕ} (r : ProbabilityDensity d) : Monotone (mass r) := by
  intro n m hnm
  apply integral_mono (cut_integrable r n) (cut_integrable r m)
  intro x
  apply min_le_min_left
  have hh : (n:ℝ) ≤ (m:ℝ) := Nat.cast_le.mpr hnm
  linarith

theorem cut_tendsto {d : ℕ} (r : ProbabilityDensity d) :
    ∀ᵐ x ∂torusMeasure d, Tendsto (fun n => cut r n x) atTop (𝓝 (r.value x)) := by
  filter_upwards [r.nonneg] with x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (r.value x)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : r.value x ≤ (n:ℝ)+1 := by
    have hcast : (N:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hn
    linarith
  simp [cut, max_eq_left hx, min_eq_left hh]

theorem mass_tendsto {d : ℕ} (r : ProbabilityDensity d) : Tendsto (mass r) atTop (𝓝 1) := by
  have h := tendsto_integral_of_dominated_convergence (F := cut r) (f := r.value)
    r.value (cut_measurable r)
    r.integrable (fun n => by
      filter_upwards [cut_le r n] with x hx
      simpa only [Real.norm_of_nonneg (cut_nonnegative r n x)] using hx) (cut_tendsto r)
  change Tendsto (fun n => ∫ x, cut r n x ∂torusMeasure d) atTop (𝓝 1)
  simpa only [r.mass] using h

def density {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) : ProbabilityDensity d where
  value := fun x => cut r n x / mass r n
  nonneg := ae_of_all _ (fun x => div_nonneg (cut_nonnegative r n x) (mass_pos r n).le)
  integrable := (cut_integrable r n).div_const _
  mass := by rw [integral_div]; exact div_self (mass_pos r n).ne'

theorem density_memLp {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    MemLp (density r n).value 2 (torusMeasure d) := by
  simpa only [density, div_eq_mul_inv, mul_comm] using
    (cut_memLp r n).const_mul (mass r n)⁻¹

theorem density_nonnegative {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) (x : Torus d) :
    0 ≤ (density r n).value x := div_nonneg (cut_nonnegative r n x) (mass_pos r n).le

theorem density_le {d : ℕ} (r : ProbabilityDensity d) (n : ℕ) :
    ∀ᵐ x ∂torusMeasure d, (density r n).value x ≤ r.value x / mass r 0 := by
  filter_upwards [cut_le r n, r.nonneg] with x hx hn
  exact (div_le_div_of_nonneg_right hx (mass_pos r n).le).trans
    (div_le_div_of_nonneg_left hn (mass_pos r 0) (mass_mono r (Nat.zero_le n)))

theorem density_tendsto {d : ℕ} (r : ProbabilityDensity d) :
    ∀ᵐ x ∂torusMeasure d,
      Tendsto (fun n => (density r n).value x) atTop (𝓝 (r.value x)) := by
  filter_upwards [cut_tendsto r] with x hx
  change Tendsto (fun n => cut r n x/mass r n) atTop (𝓝 (r.value x))
  have hm : Tendsto (fun n => mass r n) atTop (𝓝 (1:ℝ)) := mass_tendsto r
  have hh := hx.mul (hm.inv₀ (by norm_num : (1:ℝ) ≠ 0))
  simpa only [inv_one, mul_one, div_eq_mul_inv] using hh

theorem density_L1_tendsto {d : ℕ} (r : ProbabilityDensity d) :
    Tendsto (fun n => ∫ x, ‖(density r n).value x-r.value x‖ ∂torusMeasure d) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖(density r n).value x-r.value x‖) (f := fun _ => (0:ℝ))
    (fun x => r.value x/mass r 0+r.value x)
    (fun n => ((density r n).integrable.sub r.integrable).norm.aestronglyMeasurable)
    ((r.integrable.div_const _).add r.integrable) (fun n => by
      filter_upwards [density_le r n, r.nonneg] with x hx hn
      rw [norm_norm]
      calc
        ‖(density r n).value x-r.value x‖ ≤ ‖(density r n).value x‖+‖r.value x‖ := norm_sub_le _ _
        _ ≤ r.value x/mass r 0+r.value x := by
          rw [Real.norm_of_nonneg (density_nonnegative r n x), Real.norm_of_nonneg hn]
          linarith only [hx]) (by
      filter_upwards [density_tendsto r] with x hx
      simpa only [sub_self, norm_zero] using
        (hx.sub (tendsto_const_nhds (x := r.value x))).norm)
  simpa only [integral_zero] using h

theorem fourier_tendsto {d : ℕ} (r : ProbabilityDensity d) (k : Frequency d) :
    Tendsto (fun n => densityFourier (density r n).value k) atTop (𝓝 (densityFourier r.value k)) :=
  EndpointClosure.fourier_tendsto_of_L1 (density r) r (density_L1_tendsto r) k

#print axioms density_L1_tendsto
#print axioms fourier_tendsto
end Legacy.BecknerOnofri.BoundedDensityApproximation
