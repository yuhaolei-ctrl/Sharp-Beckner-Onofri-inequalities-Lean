module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Derivative decay of rational profiles: the symbol classes behind `eq:section4-profile-derivative-decay`

Lemma 4.3 of the manuscript (`lem:section4-periodization-entropy-identity`) asserts the bound

  `|∂^α η_{1/5}(x)| ≤ C_α (1+|x|)^{-22-|α|}`        (`eq:section4-profile-derivative-decay`)

which feeds the Weierstrass M-test for every differentiated periodization series.  This file proves
the bound in the coordinate-free form `‖D^k f x‖ ≤ C_k (1+‖x‖)^{m-k}` for functions `f ∈ S^m`
("symbols of order `m`"), together with the closure properties needed for `(1+25|x|²)^{-11}`:

* `IsSym.mul`      : `S^a · S^b ⊆ S^{a+b}` (Leibniz rule, `norm_iteratedFDeriv_smul_le`),
* `IsSym.add`, `IsSym.const_smul`, `IsSym.mono`, `IsSym.const`, `IsSym.clm`,
* `IsSym.inv`      : if `f ∈ S^m` and `f ≥ c (1+‖x‖)^m` with `c>0`, then `1/f ∈ S^{-m}`
  (strong induction on the derivative order, using `D(1/f) = -(1/f)² Df`),
* `IsSym.pow`.

Nothing here mentions the specific profile. -/

noncomputable section
open scoped ContDiff
set_option linter.unusedSectionVars false

namespace BecknerOnofri.V2.Eleven

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Derivative bounds of symbol type up to order `K`. -/
def SymBound (m : ℤ) (K : ℕ) (f : E → F) : Prop :=
  ∀ k : ℕ, k ≤ K → ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ k f x‖ ≤ C * (1 + ‖x‖) ^ (m - (k : ℤ))

/-- `f ∈ S^m`: smooth, with symbol bounds of every order. -/
def IsSym (m : ℤ) (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ K : ℕ, SymBound m K f

lemma one_add_norm_pos (x : E) : 0 < 1 + ‖x‖ := by positivity

lemma one_le_one_add_norm (x : E) : 1 ≤ 1 + ‖x‖ := by
  linarith [norm_nonneg x]

lemma SymBound.mono_order {m : ℤ} {K L : ℕ} {f : E → F} (h : SymBound m K f) (hL : L ≤ K) :
    SymBound m L f := fun k hk => h k (hk.trans hL)

lemma SymBound.mono_exponent {m m' : ℤ} (hm : m ≤ m') {K : ℕ} {f : E → F}
    (h : SymBound m K f) : SymBound m' K f := by
  intro k hk
  obtain ⟨C, hC⟩ := h k hk
  refine ⟨|C|, fun x => ?_⟩
  refine (hC x).trans ?_
  have h1 : (1 + ‖x‖) ^ (m - (k : ℤ)) ≤ (1 + ‖x‖) ^ (m' - (k : ℤ)) :=
    zpow_le_zpow_right₀ (one_le_one_add_norm x) (by omega)
  have h2 : 0 ≤ (1 + ‖x‖) ^ (m - (k : ℤ)) := (zpow_pos (one_add_norm_pos x) _).le
  calc C * (1 + ‖x‖) ^ (m - (k : ℤ)) ≤ |C| * (1 + ‖x‖) ^ (m - (k : ℤ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) h2
    _ ≤ |C| * (1 + ‖x‖) ^ (m' - (k : ℤ)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)

lemma IsSym.mono {m m' : ℤ} (hm : m ≤ m') {f : E → F} (h : IsSym m f) : IsSym m' f :=
  ⟨h.1, fun K => (h.2 K).mono_exponent hm⟩

/-- Leibniz rule for symbol bounds (scalar function times vector function). -/
lemma SymBound.smul {a b : ℤ} {K : ℕ} {f : E → ℝ} {g : E → F}
    (hf0 : ContDiff ℝ ∞ f) (hg0 : ContDiff ℝ ∞ g)
    (hf : SymBound a K f) (hg : SymBound b K g) :
    SymBound (a + b) K (fun x => f x • g x) := by
  intro k hk
  have hf' : ∀ i : ℕ, i ≤ K → ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ i f x‖ ≤ C * (1 + ‖x‖) ^ (a - (i : ℤ)) :=
    hf
  have hg' : ∀ i : ℕ, i ≤ K → ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ i g x‖ ≤ C * (1 + ‖x‖) ^ (b - (i : ℤ)) :=
    hg
  choose! Cf hCf using hf'
  choose! Cg hCg using hg'
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf i * Cg (k - i), fun x => ?_⟩
  refine (norm_iteratedFDeriv_smul_le hf0 hg0 x (n := k) (by exact_mod_cast le_top)).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 := hCf i (hik.trans hk) x
  have h2 := hCg (k - i) ((Nat.sub_le k i).trans hk) x
  have hw := one_add_norm_pos x
  have hch : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  have e : (1 + ‖x‖) ^ (a - (i : ℤ)) * (1 + ‖x‖) ^ (b - ((k - i : ℕ) : ℤ)) =
      (1 + ‖x‖) ^ (a + b - (k : ℤ)) := by
    rw [← zpow_add₀ hw.ne']
    congr 1
    rw [Nat.cast_sub hik]
    ring
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
      ≤ (k.choose i : ℝ) * (Cf i * (1 + ‖x‖) ^ (a - (i : ℤ))) *
          (Cg (k - i) * (1 + ‖x‖) ^ (b - ((k - i : ℕ) : ℤ))) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hch) h2 (norm_nonneg _)
          (mul_nonneg hch ((norm_nonneg _).trans h1))
    _ = ((k.choose i : ℝ) * Cf i * Cg (k - i)) * ((1 + ‖x‖) ^ (a - (i : ℤ)) *
          (1 + ‖x‖) ^ (b - ((k - i : ℕ) : ℤ))) := by ring
    _ = ((k.choose i : ℝ) * Cf i * Cg (k - i)) * (1 + ‖x‖) ^ (a + b - (k : ℤ)) := by rw [e]

lemma IsSym.mul {a b : ℤ} {f : E → ℝ} {g : E → F} (hf : IsSym a f) (hg : IsSym b g) :
    IsSym (a + b) (fun x => f x • g x) :=
  ⟨hf.1.smul hg.1, fun K => SymBound.smul hf.1 hg.1 (hf.2 K) (hg.2 K)⟩

lemma SymBound.add {m : ℤ} {K : ℕ} {f g : E → F} (hf0 : ContDiff ℝ ∞ f) (hg0 : ContDiff ℝ ∞ g)
    (hf : SymBound m K f) (hg : SymBound m K g) : SymBound m K (fun x => f x + g x) := by
  intro k hk
  obtain ⟨C₁, h₁⟩ := hf k hk
  obtain ⟨C₂, h₂⟩ := hg k hk
  refine ⟨C₁ + C₂, fun x => ?_⟩
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := k) (f := f) (g := g)
    (hf0.contDiffAt (x := x) |>.of_le (by exact_mod_cast le_top))
    (hg0.contDiffAt (x := x) |>.of_le (by exact_mod_cast le_top))
  calc ‖iteratedFDeriv ℝ k (fun x => f x + g x) x‖
      = ‖iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x‖ := by
        congr 1
    _ ≤ ‖iteratedFDeriv ℝ k f x‖ + ‖iteratedFDeriv ℝ k g x‖ := norm_add_le _ _
    _ ≤ C₁ * (1 + ‖x‖) ^ (m - (k : ℤ)) + C₂ * (1 + ‖x‖) ^ (m - (k : ℤ)) := add_le_add (h₁ x) (h₂ x)
    _ = (C₁ + C₂) * (1 + ‖x‖) ^ (m - (k : ℤ)) := by ring

lemma IsSym.add {m : ℤ} {f g : E → F} (hf : IsSym m f) (hg : IsSym m g) :
    IsSym m (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, fun K => SymBound.add hf.1 hg.1 (hf.2 K) (hg.2 K)⟩

lemma IsSym.const (c : F) : IsSym 0 (fun _ : E => c) := by
  refine ⟨contDiff_const, fun K k _ => ⟨‖c‖, fun x => ?_⟩⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [iteratedFDeriv_const_of_ne hk.ne']
    simp only [Pi.zero_apply, norm_zero]
    positivity

lemma IsSym.const_smul (c : ℝ) {m : ℤ} {f : E → F} (hf : IsSym m f) :
    IsSym m (fun x => c • f x) := by
  have := (IsSym.const (E := E) c).mul hf
  simpa using this.mono (by omega)

lemma IsSym.clm (L : E →L[ℝ] ℝ) : IsSym 1 (fun x => L x) := by
  refine ⟨L.contDiff, fun K k _ => ⟨‖L‖, fun x => ?_⟩⟩
  have hw := one_add_norm_pos x
  match k with
  | 0 =>
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, zpow_one]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  | 1 =>
    have : (1 + ‖x‖) ^ ((1 : ℤ) - ((1 : ℕ) : ℤ)) = 1 := by simp
    rw [this, mul_one, norm_iteratedFDeriv_one]
    simp
  | j + 2 =>
    have hfd : fderiv ℝ (fun x => L x) = fun _ => L := funext fun x => L.fderiv (x := x)
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x => L x) (x := x) (n := j + 1)
    rw [hfd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)] at h1
    simp only [Pi.zero_apply, norm_zero] at h1
    rw [← h1]
    positivity

lemma SymBound.neg {m : ℤ} {K : ℕ} {f : E → F} (hf : SymBound m K f) :
    SymBound m K (fun x => -f x) := by
  intro k hk
  obtain ⟨C, hC⟩ := hf k hk
  refine ⟨C, fun x => ?_⟩
  have : iteratedFDeriv ℝ k (fun x => -f x) x = -iteratedFDeriv ℝ k f x :=
    iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := k) (f := f) (x := x)
  rw [this, norm_neg]
  exact hC x

/-- Derivative of the pointwise inverse: `D(1/f) = -(1/f)² Df`. -/
lemma fderiv_inv_fun {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hne : ∀ x, f x ≠ 0) :
    fderiv ℝ (fun x => (f x)⁻¹) = fun x => (-((f x)⁻¹ ^ 2)) • fderiv ℝ f x := by
  funext x
  have hd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have h := (hasDerivAt_inv (hne x)).comp_hasFDerivAt x hd.hasFDerivAt
  have := h.fderiv
  simp only [Function.comp_def] at this
  rw [this, inv_pow]

lemma IsSym.inv {m : ℤ} {f : E → ℝ} (hf : IsSym m f) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * (1 + ‖x‖) ^ m ≤ f x) : IsSym (-m) (fun x => (f x)⁻¹) := by
  have hpos : ∀ x, 0 < f x := fun x =>
    lt_of_lt_of_le (mul_pos hc (zpow_pos (one_add_norm_pos x) _)) (hlow x)
  have hg0 : ContDiff ℝ ∞ (fun x => (f x)⁻¹) := hf.1.inv (fun x => (hpos x).ne')
  refine ⟨hg0, ?_⟩
  intro K
  induction K with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    refine ⟨c⁻¹, fun x => ?_⟩
    have hw := one_add_norm_pos x
    have hz : 0 < (1 + ‖x‖) ^ m := zpow_pos hw _
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos x)), zpow_neg]
    calc (f x)⁻¹ ≤ (c * (1 + ‖x‖) ^ m)⁻¹ := inv_anti₀ (mul_pos hc hz) (hlow x)
      _ = c⁻¹ * ((1 + ‖x‖) ^ m)⁻¹ := mul_inv _ _
  | succ K ih =>
    intro k hk
    rcases Nat.lt_or_ge k (K + 1) with h | h
    · exact ih k (by omega)
    obtain rfl : k = K + 1 := by omega
    set g : E → ℝ := fun x => (f x)⁻¹ with hgdef
    -- bounds for `-(g²)` up to order `K`
    have hgg : SymBound (-m + -m) K (fun x => g x • g x) :=
      SymBound.smul hg0 hg0 ih ih
    have hgg' : SymBound (-m + -m) K (fun x => -(g x ^ 2)) := by
      have := hgg.neg
      refine fun k hk => ?_
      obtain ⟨C, hC⟩ := this k hk
      exact ⟨C, fun x => by simpa [sq] using hC x⟩
    -- bounds for `fderiv f`
    have hDf : SymBound (m - 1) K (fderiv ℝ f) := by
      intro k hk
      obtain ⟨C, hC⟩ := hf.2 (K + 1) (k + 1) (by omega)
      refine ⟨C, fun x => ?_⟩
      have := hC x
      rw [← norm_iteratedFDeriv_fderiv] at this
      calc ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ ≤ C * (1 + ‖x‖) ^ (m - ((k + 1 : ℕ) : ℤ)) := this
        _ = C * (1 + ‖x‖) ^ (m - 1 - (k : ℤ)) := by
          congr 2
          push_cast
          ring
    have hDf0 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.1.fderiv_right (by simp)
    have hneg0 : ContDiff ℝ ∞ (fun x => -(g x ^ 2)) := (hg0.pow 2).neg
    have hprod := SymBound.smul hneg0 hDf0 hgg' hDf
    obtain ⟨C, hC⟩ := hprod K le_rfl
    refine ⟨C, fun x => ?_⟩
    have hfd := fderiv_inv_fun hf.1 (fun x => (hpos x).ne')
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := K)
    rw [hgdef, hfd] at h1
    rw [← h1]
    refine (hC x).trans (le_of_eq ?_)
    congr 2
    push_cast
    ring

lemma IsSym.pow {m : ℤ} {f : E → ℝ} (hf : IsSym m f) (n : ℕ) : IsSym (n * m) (fun x => f x ^ n) := by
  induction n with
  | zero =>
    simpa using (IsSym.const (E := E) (1 : ℝ))
  | succ n ih =>
    have := hf.mul ih
    have e : (fun x => f x • f x ^ n) = fun x => f x ^ (n + 1) := by
      funext x; simp [pow_succ']
    rw [e] at this
    refine this.mono (le_of_eq ?_)
    push_cast
    ring

lemma IsSym.finset_sum {ι : Type*} (s : Finset ι) {m : ℤ} (hm : 0 ≤ m) {f : ι → E → F}
    (hf : ∀ i ∈ s, IsSym m (f i)) : IsSym m (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (IsSym.const (E := E) (0 : F)).mono hm
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa [Finset.sum_insert ha] using h1.add h2

end BecknerOnofri.V2.Eleven
