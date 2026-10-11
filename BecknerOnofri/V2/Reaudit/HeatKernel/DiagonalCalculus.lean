module

public import Legacy.BecknerOnofri.SpectralDiagonal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-! # Diagonal operators of a Hilbert basis indexed by plain scalar families (U05/S015)

Generic functional calculus used in the truncated-potential argument for the heat kernel of
`B_α` (printed `eq:potential-kernel-domination`).  A bounded scalar family `a : ι → ℝ` defines the
bounded operator `dg e a` that multiplies the `i`-th coordinate of the Hilbert basis `e` by `a i`.
The file proves: coordinates, products, powers, norm bounds, differences and strong convergence of
operators when the symbols converge pointwise with a uniform bound.  No analysis on `L²` is used.
-/

noncomputable section
open Filter Classical
open scoped Topology BigOperators
namespace BecknerOnofri.V2.Reaudit.HeatKernel.Engine
open Legacy.BecknerOnofri.SpectralHeatInverse

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A bounded scalar family. -/
def Bdd (a : ι → ℝ) : Prop := ∃ M, ∀ i, |a i| ≤ M

theorem Bdd.mul {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i * b i) := by
  obtain ⟨M, hM⟩ := ha
  obtain ⟨N, hN⟩ := hb
  refine ⟨M * N, fun i => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM i) (hN i) (abs_nonneg _) ((abs_nonneg _).trans (hM i))

theorem Bdd.sub {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i - b i) := by
  obtain ⟨M, hM⟩ := ha
  obtain ⟨N, hN⟩ := hb
  exact ⟨M + N, fun i => (abs_sub _ _).trans (add_le_add (hM i) (hN i))⟩

theorem Bdd.of_le {a : ι → ℝ} {M : ℝ} (h : ∀ i, |a i| ≤ M) : Bdd a := ⟨M, h⟩

theorem Bdd.pow {a : ι → ℝ} (ha : Bdd a) (n : ℕ) : Bdd (fun i => a i ^ n) := by
  obtain ⟨M, hM⟩ := ha
  exact ⟨M ^ n, fun i => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM i) n⟩

/-- The diagonal operator with scalar family `a` in the Hilbert basis `e` (zero if `a` is
unbounded, which never occurs below). -/
def dg (e : HilbertBasis ι ℝ H) (a : ι → ℝ) : H →L[ℝ] H :=
  if h : Bdd a then
    diagonal e (boundedSymbol a h.choose (fun i => by
      simpa only [Real.norm_eq_abs] using h.choose_spec i))
  else 0

theorem repr_dg (e : HilbertBasis ι ℝ H) {a : ι → ℝ} (ha : Bdd a) (u : H) (i : ι) :
    e.repr (dg e a u) i = a i * e.repr u i := by
  unfold dg
  rw [dif_pos ha]
  exact repr_diagonal e _ u i

theorem dg_apply_norm_le (e : HilbertBasis ι ℝ H) {a : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) (u : H) : ‖dg e a u‖ ≤ M * ‖u‖ := by
  have hb : Bdd a := ⟨M, ha⟩
  unfold dg
  rw [dif_pos hb]
  exact diagonal_apply_norm_le e _ hM (fun i => by
    change ‖a i‖ ≤ M
    rw [Real.norm_eq_abs]; exact ha i) u

theorem dg_norm_le (e : HilbertBasis ι ℝ H) {a : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, |a i| ≤ M) : ‖dg e a‖ ≤ M :=
  (dg e a).opNorm_le_bound hM (dg_apply_norm_le e hM ha)

theorem dg_ext (e : HilbertBasis ι ℝ H) {u v : H} (h : ∀ i, e.repr u i = e.repr v i) : u = v :=
  e.repr.injective (lp.ext (funext h))

theorem dg_comp (e : HilbertBasis ι ℝ H) {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) (u : H) :
    dg e a (dg e b u) = dg e (fun i => a i * b i) u := by
  apply dg_ext e
  intro i
  rw [repr_dg e ha, repr_dg e hb, repr_dg e (ha.mul hb)]
  ring

theorem dg_pow (e : HilbertBasis ι ℝ H) {a : ι → ℝ} (ha : Bdd a) (n : ℕ) :
    (dg e a) ^ n = dg e (fun i => a i ^ n) := by
  induction n with
  | zero =>
    ext u : 1
    apply dg_ext e
    intro i
    simp only [pow_zero, ContinuousLinearMap.one_apply]
    rw [repr_dg e (Bdd.of_le (M := 1) (fun i => by simp))]
    ring
  | succ n ih =>
    ext u : 1
    rw [pow_succ, ContinuousLinearMap.mul_apply, ih]
    rw [dg_comp e (ha.pow n) ha]
    congr 1

theorem dg_sub (e : HilbertBasis ι ℝ H) {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) (u : H) :
    dg e a u - dg e b u = dg e (fun i => a i - b i) u := by
  apply dg_ext e
  intro i
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_dg e ha, repr_dg e hb, repr_dg e (ha.sub hb)]
  ring

theorem dg_smul (e : HilbertBasis ι ℝ H) {a : ι → ℝ} (ha : Bdd a) (c : ℝ) (u : H) :
    c • dg e a u = dg e (fun i => c * a i) u := by
  have hc : Bdd (fun i => c * a i) := by
    obtain ⟨M, hM⟩ := ha
    exact ⟨|c| * M, fun i => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM i) (abs_nonneg _)⟩
  apply dg_ext e
  intro i
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, repr_dg e ha, repr_dg e hc, smul_eq_mul]
  ring

/-- Parseval for a Hilbert basis in the form used here. -/
theorem hasSum_sq_repr (e : HilbertBasis ι ℝ H) (u : H) :
    HasSum (fun i => (e.repr u i) ^ 2) (‖u‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner u u
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 1
  funext i
  rw [HilbertBasis.repr_apply_apply, real_inner_comm, sq]

/-- Strong convergence of diagonal operators with uniformly bounded, pointwise convergent
symbols. -/
theorem dg_tendsto (e : HilbertBasis ι ℝ H) {a : ℕ → ι → ℝ} {b : ι → ℝ} {M : ℝ}
    (hM : ∀ n i, |a n i| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (hlim : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i))) (u : H) :
    Tendsto (fun n => dg e (a n) u) atTop (𝓝 (dg e b u)) := by
  have hbd : ∀ n, Bdd (a n) := fun n => ⟨M, hM n⟩
  have hbb : Bdd b := ⟨M, hb⟩
  have key : ∀ n, ‖dg e (a n) u - dg e b u‖ ^ 2 = ∑' i, ((a n i - b i) * e.repr u i) ^ 2 := by
    intro n
    have h := hasSum_sq_repr e (dg e (a n) u - dg e b u)
    rw [dg_sub e (hbd n) hbb] at h ⊢
    have h2 : ∀ i, (e.repr (dg e (fun i => a n i - b i) u) i) ^ 2 =
        ((a n i - b i) * e.repr u i) ^ 2 := by
      intro i; rw [repr_dg e ((hbd n).sub hbb)]
    simp_rw [h2] at h
    exact h.tsum_eq.symm
  have hsum : Tendsto (fun n => ∑' i, ((a n i - b i) * e.repr u i) ^ 2) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun n i => ((a n i - b i) * e.repr u i) ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun i => (2 * M) ^ 2 * (e.repr u i) ^ 2)
      ((hasSum_sq_repr e u).summable.mul_left _) ?_ ?_
    · simpa using this
    · intro i
      have h1 : Tendsto (fun n => a n i - b i) atTop (𝓝 0) := by
        simpa using (hlim i).sub_const (b i)
      simpa using ((h1.mul_const (e.repr u i)).pow 2)
    · refine Eventually.of_forall (fun n i => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      have h3 : |a n i - b i| ≤ 2 * M := (abs_sub _ _).trans (by linarith [hM n i, hb i])
      exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2) (sq_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h2 : Tendsto (fun n => ‖dg e (a n) u - dg e b u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [key] using hsum
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h3

end BecknerOnofri.V2.Reaudit.HeatKernel.Engine
