module

public import BecknerOnofri.V2.Reaudit.SpinChannel.ChannelFacts

@[expose] public section

/-!
# Cylinder sums for the independent spins

Given the positions `x`, the spins are independent (`spinWeight`).  The events "the first `k` spins
equal a pattern `a`" are cylinders; the finite sums below compute their conditional probabilities
`lik k a x = ∏_{j<k} P(σ_j = a_j | x)`, which depend only on `x_{<k}`, and the effect of one free
later coordinate.  These are the "conditional independence" computations of the printed proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators ENNReal
namespace BecknerOnofri.V2.Reaudit.SpinChannel
open BecknerOnofri.HighDim BecknerOnofri.HighDim.Spin BecknerOnofri.HighDim.EntropyShearer

/-- Keep the first `k` spins and set the others to `-1`. -/
def spinMask (k : ℕ) (s : Spins) : Spins := fun j => if j.val < k then s j else false

/-- Keep the first `k` positions and set the others to `0`. -/
def posMask (k : ℕ) (x : Torus 12) : Torus 12 := fun j => if j.val < k then x j else 0

/-- Spin patterns supported on the first `k` coordinates. -/
def Pat (k : ℕ) : Finset Spins := Finset.univ.filter fun a => spinMask k a = a

/-- The conditional probability of the spin pattern `a` on the first `k` coordinates, given `x`. -/
def lik (k : ℕ) (a : Spins) (x : Torus 12) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => j.val < k), bernW (torusCosines x j) (a j)

theorem spinMask_mem_Pat (k : ℕ) (s : Spins) : spinMask k s ∈ Pat k := by
  simp only [Pat, Finset.mem_filter, Finset.mem_univ, true_and]
  funext j; by_cases h : j.val < k <;> simp [spinMask, h]

theorem lik_depends (k : ℕ) (a : Spins) {x y : Torus 12} (h : ∀ j : Fin 12, j.val < k → x j = y j) :
    lik k a x = lik k a y := by
  unfold lik
  apply Finset.prod_congr rfl
  intro j hj
  have := h j (Finset.mem_filter.mp hj).2
  simp [torusCosines, this]

theorem lik_nonneg (k : ℕ) (a : Spins) (x : Torus 12) : 0 ≤ lik k a x :=
  Finset.prod_nonneg fun j _ => bernW_nonneg (torusCosines_bound x j) _

theorem lik_le_one (k : ℕ) (a : Spins) (x : Torus 12) : lik k a x ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => bernW_nonneg (torusCosines_bound x j) _) fun j _ => by
    have h := abs_le.mp (torusCosines_bound x j)
    cases a j <;> simp [bernW] <;> linarith

/-- **Cylinder sum.**  For a pattern `a` supported on the first `k` coordinates and free-coordinate
factors `G_j`, the conditional expectation over the cylinder `{σ_{<k} = a}` factorizes. -/
theorem sum_fiber_spinWeight (k : ℕ) (a : Spins) (ha : a ∈ Pat k) (x : Torus 12)
    (G : Fin 12 → Bool → ℝ) :
    ∑ s : Spins, (if spinMask k s = a then spinWeight x s * ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) else 0) =
      lik k a x * ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val),
        (bernW (torusCosines x j) true * G j true + bernW (torusCosines x j) false * G j false) := by
  have ha' : spinMask k a = a := by simpa [Pat] using ha
  have key := sum_spinWeight_mul_prod x
    (fun j b => if j.val < k then (if b = a j then 1 else 0) else G j b)
  have hsplit : ∀ s : Spins, (∏ j, (if j.val < k then (if s j = a j then (1 : ℝ) else 0) else G j (s j))) =
      (if spinMask k s = a then 1 else 0) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) := by
    intro s
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin 12 => j.val < k)]
    have h1 : ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => j.val < k),
        (if j.val < k then (if s j = a j then (1 : ℝ) else 0) else G j (s j)) =
        if spinMask k s = a then 1 else 0 := by
      rw [Finset.prod_congr rfl (g := fun j => if s j = a j then (1 : ℝ) else 0)
        (fun j hj => by simp [(Finset.mem_filter.mp hj).2])]
      rw [Finset.prod_boole]
      congr 1
      apply propext
      constructor
      · intro h
        funext j
        by_cases hj : j.val < k
        · simpa [spinMask, hj] using h j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        · have := congrFun ha' j
          simpa [spinMask, hj] using this.symm
      · intro h j hj
        have := congrFun h j
        simpa [spinMask, (Finset.mem_filter.mp hj).2] using this
    have h2 : ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => ¬ j.val < k),
        (if j.val < k then (if s j = a j then (1 : ℝ) else 0) else G j (s j)) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) := by
      apply Finset.prod_congr (by ext j; simp)
      intro j hj
      have hjk : k ≤ j.val := by simpa using hj
      simp [Nat.not_lt.mpr hjk]
    rw [h1, h2]
  simp_rw [hsplit] at key
  have lhs : ∀ s : Spins, spinWeight x s * ((if spinMask k s = a then (1 : ℝ) else 0) *
      ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j)) =
      (if spinMask k s = a then spinWeight x s * ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) else 0) := by
    intro s; split_ifs <;> simp
  simp_rw [lhs] at key
  rw [key]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j : Fin 12 => j.val < k)]
  congr 1
  · unfold lik
    apply Finset.prod_congr rfl
    intro j hj
    have hjk := (Finset.mem_filter.mp hj).2
    simp [hjk, bernW]
    cases a j <;> simp
  · apply Finset.prod_congr (by ext j; simp)
    intro j hj
    have hjk : k ≤ j.val := by simpa using hj
    simp [Nat.not_lt.mpr hjk]


/-- Grouping the spin sum by the masked pattern. -/
theorem sum_spinWeight_mask (k : ℕ) (x : Torus 12) (Θ : Spins → ℝ) (G : Fin 12 → Bool → ℝ) :
    ∑ s : Spins, spinWeight x s * Θ (spinMask k s) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) =
      ∑ a ∈ Pat k, Θ a * (lik k a x * ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val),
        (bernW (torusCosines x j) true * G j true + bernW (torusCosines x j) false * G j false)) := by
  have h1 : ∀ s : Spins, spinWeight x s * Θ (spinMask k s) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) =
      ∑ a ∈ Pat k, Θ a * (if spinMask k s = a then spinWeight x s *
        ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => k ≤ j.val), G j (s j) else 0) := by
    intro s
    rw [Finset.sum_eq_single (spinMask k s)]
    · simp; ring
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h; exact absurd (spinMask_mem_Pat k s) h
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum, sum_fiber_spinWeight k a ha x G]

theorem sum_spinWeight_mask_one (k : ℕ) (x : Torus 12) (Θ : Spins → ℝ) :
    ∑ s : Spins, spinWeight x s * Θ (spinMask k s) = ∑ a ∈ Pat k, lik k a x * Θ a := by
  have h := sum_spinWeight_mask k x Θ (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at h
  have hfac : ∀ j, (bernW (torusCosines x j) true + bernW (torusCosines x j) false) = 1 :=
    fun j => bernW_add _
  simp only [hfac, Finset.prod_const_one, mul_one] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _; ring

/-- The conditional independence of the current spin from the earlier spins given `x`
(`E[σ_i 1{σ_{<i} = a} | x] = cos(2πx_i) P(σ_{<i} = a | x)`). -/
theorem sum_spinWeight_mask_spin (i : Fin 12) (x : Torus 12) (Θ : Spins → ℝ) :
    ∑ s : Spins, spinWeight x s * Θ (spinMask i.val s) * (if s i then (1 : ℝ) else -1) =
      torusCosines x i * ∑ a ∈ Pat i.val, lik i.val a x * Θ a := by
  have h := sum_spinWeight_mask i.val x Θ (fun j b => if j = i then (if b then (1 : ℝ) else -1) else 1)
  have hi : i ∈ Finset.univ.filter (fun j : Fin 12 => i.val ≤ j.val) := by simp
  have e1 : ∀ s : Spins, ∏ j ∈ Finset.univ.filter (fun j : Fin 12 => i.val ≤ j.val),
      (if j = i then (if s j then (1 : ℝ) else -1) else 1) = if s i then (1 : ℝ) else -1 := by
    intro s
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd hi h
  simp_rw [e1] at h
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj, bernW_add]) (fun h => absurd hi h)] at h
  simp only [bernW, ite_true, Bool.false_eq_true, ite_false] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _; ring

end BecknerOnofri.V2.Reaudit.SpinChannel
