import BecknerOnofri.SelectedNumericalModel

/-! Certified enclosure updates specialize to the original selected maximizer
without an abstract monotonicity or omitted-tail assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology BigOperators
namespace BecknerOnofri.HighDim.SelectedNumericalModel
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment SubcriticalEuler SmoothFourier
open GinibreCovariance GridGibbsComparison ContinuousGibbs

/-- The actual normalized Gibbs density mode, independently of the iteration. -/
def densityMode (u : TorusL2 12) (k : Frequency 12) : ℝ :=
  (densityFourier (gibbsValue u) k).re

/-- Its genuine L² norm, expressed using the original L² potential. -/
def densityNorm (u : TorusL2 12) : ℝ :=
  Real.sqrt (∫ x, (gibbsValue u x)^2 ∂torusMeasure 12)

theorem densityNorm_eq {u : TorusL2 12} (hu : Selected u) :
    densityNorm u=gibbsL2Norm (potential u) := by
  unfold densityNorm gibbsL2Norm
  congr 1
  apply integral_congr_ae
  filter_upwards [smoothGibbsValue_ae_eq u (fourier_norm_summable hu)] with x hx
  rw [← normalized_apply,potential_normalized hu,hx]

theorem amplitude_cap {u : TorusL2 12} (hu : Selected u) {k : Frequency 12}
    (hk : k≠0) {X : ℝ} (hX : densityMode u k≤X) :
    amplitude u k≤(1/frequencyLength k^12)*X := by
  rw [Bridge.frequencyLength_eq,one_div]
  rw [amplitude_euler hu hk,← density_expectation hu]
  exact mul_le_mul_of_nonneg_left hX (show 0≤(frequencyRadius k^12)⁻¹ by positivity)

theorem omitted_mass_of_norm {u : TorusL2 12} (hu : Selected u)
    (A : Finset (Frequency 12)) {M : ℝ} (hM : densityNorm u≤M) :
    (∑' k, CommonEnclosure.omitted A (amplitude u) k)≤IterationOmittedTail.tailConstant A*M := by
  apply (omitted_mass_bound hu A).trans
  rw [← densityNorm_eq hu]
  exact mul_le_mul_of_nonneg_left hM (IterationOmittedTail.tailConstant_nonneg A)

/-- The source's complete retained-coefficient minimum update, now for the
actual Gibbs Fourier coefficients of every selected endpoint maximizer. -/
theorem selected_coefficient_update {N : ℕ} [NeZero N]
    {u : TorusL2 12} (hu : Selected u) (A : Finset (Frequency 12))
    (b : Frequency 12 → ℝ) (hb : ∀ k∈A,amplitude u k≤b k)
    (M : ℝ) (hM : densityNorm u≤M) (r : Frequency 12) (X : ℝ) (hX : densityMode u r≤X) :
    let δ := IterationOmittedTail.tailConstant A*M
    let v := cosinePotential (fun k : A => b k) (fun k => k.val)
    let G := gridExpectation (N := N) v (cosine r)
    densityMode u r≤min X (min (G+δ) (1-(1-G)*Real.exp (-2*δ))) := by
  change densityMode u r≤_
  rw [densityMode,density_expectation hu]
  exact CommonEnclosure.coefficient_min_update (N := N) A (amplitude u) b id
    (amplitude_nonneg hu) (amplitude_summable hu) hb _ (omitted_mass_of_norm hu A hM)
    r X (by simpa only [densityMode,density_expectation hu,potential] using hX)

/-- The source's complete minimum L² update for the same actual density. -/
theorem selected_norm_update {N : ℕ} [NeZero N]
    {u : TorusL2 12} (hu : Selected u) (A : Finset (Frequency 12))
    (b : Frequency 12 → ℝ) (hb : ∀ k∈A,amplitude u k≤b k)
    (M : ℝ) (hM : densityNorm u≤M) (L : ℝ) (hL : 0<L)
    (hLZ : L≤ContinuousGibbs.partition (cosinePotential (fun k : A => b k) (fun k => k.val))) :
    let δ := IterationOmittedTail.tailConstant A*M
    let v := cosinePotential (fun k : A => b k) (fun k => k.val)
    densityNorm u≤min M (Real.exp δ*Real.sqrt (gridMean (N := N) (exponential ((2:ℝ) • v)))/L) := by
  rw [densityNorm_eq hu]
  exact CommonEnclosure.norm_min_update (N := N) A (amplitude u) b id
    (amplitude_nonneg hu) (amplitude_summable hu) hb _ (omitted_mass_of_norm hu A hM)
    L hL hLZ M (by simpa only [densityNorm_eq hu,potential] using hM)

#print axioms densityNorm_eq
#print axioms selected_coefficient_update
#print axioms selected_norm_update
end BecknerOnofri.HighDim.SelectedNumericalModel
