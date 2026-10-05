import Legacy.BecknerOnofri.WienerFourier
import Mathlib.Data.List.OfFn

/-! Absolutely convergent exponential expansions indexed by genuine finite words. -/
noncomputable section
open scoped BigOperators
namespace Legacy.BecknerOnofri.ExponentialWordSeries

private theorem product_norm_summable {K ι : Type*} [RCLike K] {n : ℕ}
    (f : Fin n → ι → K) (hf : ∀ i, Summable (fun j => ‖f i j‖)) :
    Summable (fun j : Fin n → ι => ‖∏ i, f i (j i)‖) := by
  induction n with
  | zero => exact (hasSum_fintype _).summable
  | succ n ih =>
    have hh := (hf 0).mul_norm (ih (fun i => f i.succ) (fun i => hf i.succ))
    apply (Fin.consEquiv (fun _ : Fin (n+1) => ι)).summable_iff.mp
    simpa only [Function.comp_def,Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ] using hh

private theorem product_tsum {K ι : Type*} [RCLike K] {n : ℕ}
    (f : Fin n → ι → K) (hf : ∀ i, Summable (fun j => ‖f i j‖)) :
    (∏ i, ∑' j : ι, f i j) = ∑' j : Fin n → ι, ∏ i, f i (j i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ,ih (fun i => f i.succ) (fun i => hf i.succ)]
    rw [tsum_mul_tsum_of_summable_norm (hf 0)
      (product_norm_summable (fun i => f i.succ) (fun i => hf i.succ))]
    simpa only [Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ] using
      (Fin.consEquiv (fun _ : Fin (n+1) => ι)).tsum_eq (fun j : Fin (n+1) → ι => ∏ i, f i (j i))

def word {K ι : Type*} [RCLike K] (a : ι → K) (xs : List ι) : K :=
  (xs.length.factorial : K)⁻¹ * (xs.map a).prod

def tuple {K ι : Type*} [RCLike K] (a : ι → K) (p : Σ n : ℕ, Fin n → ι) : K :=
  (p.1.factorial : K)⁻¹ * ∏ i, a (p.2 i)

theorem tuple_norm_sum {K ι : Type*} [RCLike K] (a : ι → K)
    (ha : Summable (fun j => ‖a j‖)) (n : ℕ) :
    (∑' j : Fin n → ι, ‖tuple a ⟨n,j⟩‖) = (n.factorial : ℝ)⁻¹*(∑' j, ‖a j‖)^n := by
  simp only [tuple,norm_mul,norm_inv,RCLike.norm_natCast,norm_prod,tsum_mul_left]
  rw [← product_tsum (fun _ : Fin n => fun j => ‖a j‖) (fun _ => ha.norm)]
  simp

theorem tuple_norm_summable {K ι : Type*} [RCLike K] (a : ι → K)
    (ha : Summable (fun j => ‖a j‖)) : Summable (fun p : Σ n : ℕ, Fin n → ι => ‖tuple a p‖) := by
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg (tuple a p))).mpr
  constructor
  · intro n
    have hh := (product_norm_summable (fun _ : Fin n => a) (fun _ => ha)).mul_left (n.factorial : ℝ)⁻¹
    simpa only [tuple,norm_mul,norm_inv,RCLike.norm_natCast] using hh
  · simp_rw [tuple_norm_sum a ha]
    simpa only [smul_eq_mul,Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' j, ‖a j‖)).summable

theorem tuple_sum {K ι : Type*} [RCLike K] (a : ι → K) (ha : Summable (fun j => ‖a j‖)) (n : ℕ) :
    (∑' j : Fin n → ι, tuple a ⟨n,j⟩) = (n.factorial : K)⁻¹*(∑' j, a j)^n := by
  rw [show (fun j : Fin n → ι => tuple a ⟨n,j⟩) =
    (fun j => (n.factorial : K)⁻¹*∏ i, a (j i)) from rfl,tsum_mul_left,
    ← product_tsum (fun _ : Fin n => a) (fun _ => ha)]
  simp

theorem word_norm_summable {K ι : Type*} [RCLike K] (a : ι → K)
    (ha : Summable (fun j => ‖a j‖)) : Summable (fun xs : List ι => ‖word a xs‖) := by
  apply List.equivSigmaTuple.symm.summable_iff.mp
  simpa only [Function.comp_def,List.equivSigmaTuple_symm_apply,word,List.length_ofFn,
    List.map_ofFn,List.prod_ofFn,tuple] using tuple_norm_summable a ha

theorem complex_word_sum {ι : Type*} (a : ι → ℂ) (ha : Summable (fun j => ‖a j‖)) :
    (∑' xs : List ι, word a xs) = Complex.exp (∑' j, a j) := by
  rw [← List.equivSigmaTuple.symm.tsum_eq (word a)]
  simp only [List.equivSigmaTuple_symm_apply,word,List.length_ofFn,List.map_ofFn,List.prod_ofFn]
  change (∑' p : Σ n : ℕ, Fin n → ι, tuple a p) = _
  rw [(tuple_norm_summable a ha).of_norm.tsum_sigma]
  simp_rw [tuple_sum a ha]
  simpa only [smul_eq_mul,Complex.exp_eq_exp_ℂ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (∑' j, a j)).tsum_eq

theorem real_word_sum {ι : Type*} (a : ι → ℝ) (ha : Summable (fun j => ‖a j‖)) :
    (∑' xs : List ι, word a xs) = Real.exp (∑' j, a j) := by
  rw [← List.equivSigmaTuple.symm.tsum_eq (word a)]
  simp only [List.equivSigmaTuple_symm_apply,word,List.length_ofFn,List.map_ofFn,List.prod_ofFn]
  change (∑' p : Σ n : ℕ, Fin n → ι, tuple a p) = _
  rw [(tuple_norm_summable a ha).of_norm.tsum_sigma]
  simp_rw [tuple_sum a ha]
  simpa only [smul_eq_mul,Real.exp_eq_exp_ℝ] using
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (∑' j, a j)).tsum_eq

#print axioms complex_word_sum
#print axioms real_word_sum
end Legacy.BecknerOnofri.ExponentialWordSeries
