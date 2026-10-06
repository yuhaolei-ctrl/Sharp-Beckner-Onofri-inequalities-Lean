module

public import Mathlib.Analysis.Real.Pi.Bounds
public import BecknerOnofri.ComplementSobolev
public import Legacy.TorusEndpoint.GreenMultiplierSummability

@[expose] public section

noncomputable section
open Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SobolevEmbedding
open Legacy.TorusEndpoint.GreenMultiplierSummability

theorem summable_int_weight {p : ℝ} (hp : (1/2:ℝ)<p) :
    Summable (fun n : ℤ => (1+(n:ℝ)^2)^(-p)) := by
  have hb := Real.summable_abs_int_rpow (show 1<2*p by linarith)
  apply hb.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0:ℤ)] with n hn
  have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
  have he : ((n:ℝ)^2)^(-p)=|(n:ℝ)|^(-(2*p)) := by
    rw [← sq_abs,← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg _)]
    congr 1
    norm_num
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _),← he]
  exact Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hn') (by linarith) (by linarith)

def productWeight (d : ℕ) (p : ℝ) (k : Frequency d) : ℝ :=
  ∏ i : Fin d,(1+(k i:ℝ)^2)^(-p)

theorem summable_productWeight (d : ℕ) {p : ℝ} (hp : (1/2:ℝ)<p) :
    Summable (productWeight d p) := by
  induction d with
  | zero => exact (hasSum_fintype _).summable
  | succ d ih =>
    have h := (summable_int_weight hp).mul_of_nonneg ih (fun n => by positivity)
      (fun k => Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (by positivity) _))
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℤ)).summable_iff.mp
    simpa [Function.comp_def,productWeight,Fin.prod_univ_succ,Fin.consEquiv,mul_comm] using h

theorem inverse_scale_square_le_product {d : ℕ} (hd : 0<d) {s : ℝ} (hs : (d:ℝ)/2<s)
    (k : Frequency d) : (sobolevScale s k)⁻¹^2≤productWeight d (s/d) k := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hs' : 0<s := (half_pos hd').trans hs
  have hp : 0<s/d := div_pos hs' hd'
  let B : ℝ := 1+(2*Real.pi*frequencyLength k)^2
  have hB : 0<B := by dsimp [B]; positivity
  have hki (i : Fin d) : 1+(k i:ℝ)^2≤B := by
    have h1 : (k i:ℝ)^2≤radiusSq k := Finset.single_le_sum
      (fun j hj => sq_nonneg (k j:ℝ)) (Finset.mem_univ i)
    have h2 : frequencyLength k^2=radiusSq k := frequencyRadius_sq k
    have hr : 0≤frequencyLength k := Real.sqrt_nonneg _
    have h3 : frequencyLength k≤2*Real.pi*frequencyLength k := by
      nlinarith [Real.pi_gt_three]
    have h4 := pow_le_pow_left₀ hr h3 2
    dsimp [B]
    nlinarith
  have hprod : (∏ i : Fin d,(1+(k i:ℝ)^2)^(s/d))≤B^s := by
    calc
      _ ≤ ∏ _ : Fin d,B^(s/d) := Finset.prod_le_prod₀
        (fun i hi => Real.rpow_nonneg (by positivity) _)
        (fun i hi => Real.rpow_le_rpow (by positivity) (hki i) hp.le)
      _ = (B^(s/d))^d := by simp
      _ = B^s := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hB.le]
        congr 1
        exact div_mul_cancel₀ s hd'.ne'
  have hprodpos : 0<∏ i : Fin d,(1+(k i:ℝ)^2)^(s/d) := by
    apply Finset.prod_pos
    intro i hi
    positivity
  have h := inv_anti₀ hprodpos hprod
  have he : (sobolevScale s k)⁻¹^2=(B^s)⁻¹ := by rw [inv_pow,sobolevScale_sq]
  rw [he]
  have hm (i : Fin d) : (1+(k i:ℝ)^2)^(-(s/d))=((1+(k i:ℝ)^2)^(s/d))⁻¹ :=
    Real.rpow_neg (by positivity) _
  have hM : productWeight d (s/d) k = (∏ i : Fin d,(1+(k i:ℝ)^2)^(s/d))⁻¹ := by
    simp only [productWeight,hm,Finset.prod_inv_distrib]
  rw [hM]
  exact h

#print axioms inverse_scale_square_le_product
end BecknerOnofri.HighDim.SobolevEmbedding
