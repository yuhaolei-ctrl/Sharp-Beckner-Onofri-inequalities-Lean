module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Second-order jets at the origin

`Jet2 φ c0 c1 c2` means `φ(t) = c0 + c1 t + c2 t² + O(t³)` as `t → 0`.  The rules below
(sum, product, reciprocal at value one, logarithm at value one) are the finite asymptotic
calculus used for the origin expansions of Appendix A.3.
-/

noncomputable section
open Filter Topology Asymptotics
open scoped BigOperators
namespace BecknerOnofri.V2.FiniteState

/-- `φ(t) = c0 + c1 t + c2 t² + O(t³)` at `t = 0`. -/
def Jet2 (φ : ℝ → ℝ) (c0 c1 c2 : ℝ) : Prop :=
  (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3

theorem isBigO_pow_one (n : ℕ) : (fun t : ℝ => t ^ n) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  Filter.Tendsto.isBigO_one ℝ (c := (0 : ℝ) ^ n) ((continuous_pow n).tendsto 0)

theorem isBigO_pow_pow {m n : ℕ} (h : n ≤ m) :
    (fun t : ℝ => t ^ m) =O[𝓝 0] fun t : ℝ => t ^ n := by
  rcases h.eq_or_lt with rfl | hlt
  · exact Asymptotics.isBigO_refl _ _
  · exact (Asymptotics.isLittleO_pow_pow hlt).isBigO

theorem isBigO_pow_id {n : ℕ} (h : 1 ≤ n) : (fun t : ℝ => t ^ n) =O[𝓝 0] fun t : ℝ => t := by
  simpa using isBigO_pow_pow h (n := 1)

theorem isBigO_poly2 (c0 c1 c2 : ℝ) :
    (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
  Filter.Tendsto.isBigO_one ℝ (c := c0 + c1 * 0 + c2 * 0 ^ 2)
    ((by fun_prop : Continuous fun t : ℝ => c0 + c1 * t + c2 * t ^ 2).tendsto 0)

theorem Jet2.isBigO_one {φ : ℝ → ℝ} {c0 c1 c2 : ℝ} (h : Jet2 φ c0 c1 c2) :
    φ =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have h1 : (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    Asymptotics.IsBigO.trans (show (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =O[𝓝 0]
      fun t : ℝ => t ^ 3 from h) (isBigO_pow_one 3)
  have := h1.add (isBigO_poly2 c0 c1 c2)
  simpa using this

theorem Jet2.of_isBigO {φ : ℝ → ℝ} (h : φ =O[𝓝 0] fun t : ℝ => t ^ 3) : Jet2 φ 0 0 0 := by
  unfold Jet2; simpa using h

theorem Jet2.tendsto {φ : ℝ → ℝ} {c0 c1 c2 : ℝ} (h : Jet2 φ c0 c1 c2) :
    Tendsto φ (𝓝 0) (𝓝 c0) := by
  have h1 : (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =o[𝓝 0] fun _ : ℝ => (1 : ℝ) :=
    (show (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 from h).trans_isLittleO
      (by simpa using Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 0) (n := 3) (by norm_num))
  rw [Asymptotics.isLittleO_one_iff] at h1
  have h2 : Tendsto (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2) (𝓝 0) (𝓝 c0) := by
    have := (by fun_prop : Continuous fun t : ℝ => c0 + c1 * t + c2 * t ^ 2).tendsto 0
    simpa using this
  simpa using h1.add h2

theorem Jet2.add {φ ψ : ℝ → ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} (h : Jet2 φ c0 c1 c2)
    (h' : Jet2 ψ d0 d1 d2) : Jet2 (fun t => φ t + ψ t) (c0 + d0) (c1 + d1) (c2 + d2) := by
  unfold Jet2 at *
  refine (h.add h').congr_left ?_
  intro t; ring

theorem Jet2.sub {φ ψ : ℝ → ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} (h : Jet2 φ c0 c1 c2)
    (h' : Jet2 ψ d0 d1 d2) : Jet2 (fun t => φ t - ψ t) (c0 - d0) (c1 - d1) (c2 - d2) := by
  unfold Jet2 at *
  refine (h.sub h').congr_left ?_
  intro t; ring

theorem Jet2.const_mul {φ : ℝ → ℝ} {c0 c1 c2 : ℝ} (a : ℝ) (h : Jet2 φ c0 c1 c2) :
    Jet2 (fun t => a * φ t) (a * c0) (a * c1) (a * c2) := by
  unfold Jet2 at *
  refine (h.const_mul_left a).congr_left ?_
  intro t; ring

theorem Jet2.const (c : ℝ) : Jet2 (fun _ => c) c 0 0 := by
  unfold Jet2; simpa using (Asymptotics.isBigO_zero (fun t : ℝ => t ^ 3) (𝓝 (0 : ℝ)))

theorem Jet2.id : Jet2 (fun t => t) 0 1 0 := by
  unfold Jet2; simpa using (Asymptotics.isBigO_zero (fun t : ℝ => t ^ 3) (𝓝 (0 : ℝ)))

theorem Jet2.congr {φ ψ : ℝ → ℝ} {c0 c1 c2 : ℝ} (h : Jet2 φ c0 c1 c2) (e : ∀ t, ψ t = φ t) :
    Jet2 ψ c0 c1 c2 := by
  have : ψ = φ := funext e
  rw [this]; exact h

theorem Jet2.coeff {φ : ℝ → ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} (h : Jet2 φ c0 c1 c2) (e0 : c0 = d0)
    (e1 : c1 = d1) (e2 : c2 = d2) : Jet2 φ d0 d1 d2 := by
  subst e0 e1 e2; exact h

theorem Jet2.sum {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℝ} {c0 c1 c2 : ι → ℝ}
    (h : ∀ i ∈ s, Jet2 (φ i) (c0 i) (c1 i) (c2 i)) :
    Jet2 (fun t => ∑ i ∈ s, φ i t) (∑ i ∈ s, c0 i) (∑ i ∈ s, c1 i) (∑ i ∈ s, c2 i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Jet2.const 0
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1.add h2

theorem Jet2.mul {φ ψ : ℝ → ℝ} {c0 c1 c2 d0 d1 d2 : ℝ} (h : Jet2 φ c0 c1 c2)
    (h' : Jet2 ψ d0 d1 d2) :
    Jet2 (fun t => φ t * ψ t) (c0 * d0) (c0 * d1 + c1 * d0) (c0 * d2 + c1 * d1 + c2 * d0) := by
  have hψ := h'.isBigO_one
  have hP := isBigO_poly2 c0 c1 c2
  have hR : (fun t : ℝ => φ t - (c0 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h
  have hR' : (fun t : ℝ => ψ t - (d0 + d1 * t + d2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h'
  have t1 : (fun t : ℝ => (φ t - (c0 + c1 * t + c2 * t ^ 2)) * ψ t) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    have := hR.mul hψ
    simpa using this
  have t2 : (fun t : ℝ => (c0 + c1 * t + c2 * t ^ 2) * (ψ t - (d0 + d1 * t + d2 * t ^ 2))) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    have := hP.mul hR'
    simpa using this
  have t3 : (fun t : ℝ => (c1 * d2 + c2 * d1) * t ^ 3 + c2 * d2 * t ^ 4) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
    refine Asymptotics.IsBigO.add ?_ ?_
    · exact (Asymptotics.isBigO_refl _ _).const_mul_left _
    · exact (isBigO_pow_pow (by norm_num : 3 ≤ 4)).const_mul_left _
  unfold Jet2
  refine ((t1.add t2).add t3).congr_left ?_
  intro t
  ring

/-- Reciprocal of a jet with value one. -/
theorem Jet2.inv_one {φ : ℝ → ℝ} {c1 c2 : ℝ} (h : Jet2 φ 1 c1 c2) :
    Jet2 (fun t => (φ t)⁻¹) 1 (-c1) (c1 ^ 2 - c2) := by
  have hφc : Tendsto φ (𝓝 0) (𝓝 1) := h.tendsto
  have hinv : Tendsto (fun t => (φ t)⁻¹) (𝓝 0) (𝓝 1) := by
    simpa using hφc.inv₀ one_ne_zero
  have hinvO := Filter.Tendsto.isBigO_one ℝ hinv
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ≠ 0 := hφc.eventually_ne one_ne_zero
  have hR : (fun t : ℝ => φ t - (1 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h
  have hQ := isBigO_poly2 1 (-c1) (c1 ^ 2 - c2)
  have t1 : (fun t : ℝ => (φ t - (1 + c1 * t + c2 * t ^ 2)) * (1 + (-c1) * t + (c1 ^ 2 - c2) * t ^ 2)
      * (φ t)⁻¹) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := (hR.mul hQ).mul hinvO
    simpa using this
  have t2 : (fun t : ℝ => (-(c1 ^ 3 - 2 * c1 * c2) * t ^ 3 - c2 * (c1 ^ 2 - c2) * t ^ 4) * (φ t)⁻¹)
      =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have h3 : (fun t : ℝ => -(c1 ^ 3 - 2 * c1 * c2) * t ^ 3 - c2 * (c1 ^ 2 - c2) * t ^ 4) =O[𝓝 0]
        fun t : ℝ => t ^ 3 := by
      refine Asymptotics.IsBigO.sub ?_ ?_
      · exact (Asymptotics.isBigO_refl _ _).const_mul_left _
      · exact (isBigO_pow_pow (by norm_num : 3 ≤ 4)).const_mul_left _
    have := h3.mul hinvO
    simpa using this
  unfold Jet2
  refine (t2.sub t1).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hne] with t ht
  field_simp
  ring

/-- Finite product of jets of the form `1 + u t + v_k t²`. -/
theorem Jet2.prod_range (n : ℕ) {φ : ℕ → ℝ → ℝ} {u : ℝ} {v : ℕ → ℝ}
    (h : ∀ k < n, Jet2 (φ k) 1 u (v k)) :
    Jet2 (fun t => ∏ k ∈ Finset.range n, φ k t) 1 ((n : ℝ) * u)
      (∑ k ∈ Finset.range n, v k + ((n : ℝ) * ((n : ℝ) - 1) / 2) * u ^ 2) := by
  induction n with
  | zero => simpa using Jet2.const 1
  | succ n ih =>
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h n (Nat.lt_succ_self n)
    have h3 := h1.mul h2
    refine (h3.congr (fun t => by simp [Finset.prod_range_succ])).coeff (by ring) ?_ ?_
    · push_cast; ring
    · simp only [Finset.sum_range_succ]; push_cast; ring

/-- A real-variable remainder estimate: `|log(1+z) - (z - z²/2)| ≤ 2|z|³` for `|z| ≤ 1/2`. -/
theorem abs_log_one_add_sub_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - (z - z ^ 2 / 2)| ≤ 2 * |z| ^ 3 := by
  have h1 : |(-z)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 2
  simp only [abs_neg] at h
  have hsum : (∑ i ∈ Finset.range 2, (-z) ^ (i + 1) / ((i : ℝ) + 1)) = -z + z ^ 2 / 2 := by
    simp [Finset.sum_range_succ]; ring
  rw [hsum, show (1 : ℝ) - -z = 1 + z by ring] at h
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hden : 1 / 2 ≤ 1 - |z| := by linarith
  have h2 : |z| ^ 3 / (1 - |z|) ≤ 2 * |z| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hz0 3]
  have e : Real.log (1 + z) - (z - z ^ 2 / 2) = -z + z ^ 2 / 2 + Real.log (1 + z) := by ring
  rw [e]
  exact h.trans h2

/-- Logarithm of a jet with value one. -/
theorem Jet2.log_one {φ : ℝ → ℝ} {c1 c2 : ℝ} (h : Jet2 φ 1 c1 c2) :
    Jet2 (fun t => Real.log (φ t)) 0 c1 (c2 - c1 ^ 2 / 2) := by
  have hR : (fun t : ℝ => φ t - (1 + c1 * t + c2 * t ^ 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := h
  set z : ℝ → ℝ := fun t => φ t - 1 with hzdef
  have hzO : z =O[𝓝 0] fun t : ℝ => t := by
    have e : z = fun t => (φ t - (1 + c1 * t + c2 * t ^ 2)) + (c1 * t + c2 * t ^ 2) := by
      funext t; simp only [hzdef]; ring
    rw [e]
    refine Asymptotics.IsBigO.add (hR.trans (isBigO_pow_id (by norm_num : 1 ≤ 3))) ?_
    refine Asymptotics.IsBigO.add ((Asymptotics.isBigO_refl _ _).const_mul_left _) ?_
    exact (isBigO_pow_id (by norm_num : 1 ≤ 2)).const_mul_left _
  have hz2 : (fun t : ℝ => z t - c1 * t) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    have e : (fun t : ℝ => z t - c1 * t) =
        fun t => (φ t - (1 + c1 * t + c2 * t ^ 2)) + c2 * t ^ 2 := by
      funext t; simp only [hzdef]; ring
    rw [e]
    exact (hR.trans (isBigO_pow_pow (by norm_num : 2 ≤ 3))).add
      ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have hz1 : (fun t : ℝ => z t + c1 * t) =O[𝓝 0] fun t : ℝ => t :=
    hzO.add ((Asymptotics.isBigO_refl _ _).const_mul_left _)
  have hsq : (fun t : ℝ => z t ^ 2 - c1 ^ 2 * t ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have := hz2.mul hz1
    refine this.congr' (Filter.Eventually.of_forall fun t => by simp only; ring) ?_
    exact Filter.Eventually.of_forall fun t => by simp only; ring
  have hz3 : (fun t : ℝ => z t ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := hzO.pow 3
  have hzt : Tendsto z (𝓝 0) (𝓝 0) := by
    have := h.tendsto
    simpa [hzdef] using this.sub_const 1
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |z t| ≤ 1 / 2 := by
    have := (hzt.abs).eventually (Iic_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
    simpa using this
  have hlog : (fun t : ℝ => Real.log (φ t) - (z t - z t ^ 2 / 2)) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
    have hb : (fun t : ℝ => Real.log (φ t) - (z t - z t ^ 2 / 2)) =O[𝓝 0] fun t : ℝ => z t ^ 3 := by
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [hsmall] with t ht
      have := abs_log_one_add_sub_le ht
      have e : φ t = 1 + z t := by simp only [hzdef]; ring
      rw [e]
      simpa [abs_pow] using this
    exact hb.trans hz3
  unfold Jet2
  have := (hlog.add (hR.sub (hsq.const_mul_left (1 / 2))))
  refine this.congr_left ?_
  intro t
  simp only [hzdef]
  ring

end BecknerOnofri.V2.FiniteState
