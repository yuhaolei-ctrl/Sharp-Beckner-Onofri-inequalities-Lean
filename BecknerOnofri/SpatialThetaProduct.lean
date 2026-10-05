import BecknerOnofri.SpatialThetaDiagonal
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-! The convergent normalized Jacobi product, its positivity, log-concavity,
and diagonal comparison. This file does not assume or assert its identification
with the actual spatial theta Fourier series; that identity remains separate. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace BecknerOnofri.HighDim.SpatialThetaProduct

def qMode (t : ℝ) (n : ℕ) : ℝ := Real.exp (-t*(2*(n:ℝ)+1))
def coefficient (t : ℝ) (n : ℕ) : ℝ := 4*qMode t n/(1+qMode t n)^2
def factor (t r : ℝ) (n : ℕ) : ℝ := 1-coefficient t n*r
def logProduct (t r : ℝ) : ℝ := ∑' n, Real.log (factor t r n)
def jacobiProduct (t r : ℝ) : ℝ := ∏' n, factor t r n

theorem qMode_pos (t : ℝ) (n : ℕ) : 0<qMode t n := Real.exp_pos _

theorem qMode_lt_one {t : ℝ} (ht : 0<t) (n : ℕ) : qMode t n<1 := by
  apply Real.exp_lt_one_iff.mpr
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos ht) (by linarith)

theorem coefficient_pos (t : ℝ) (n : ℕ) : 0<coefficient t n := by
  have hp := qMode_pos t n
  unfold coefficient
  positivity

theorem coefficient_lt_one {t : ℝ} (ht : 0<t) (n : ℕ) : coefficient t n<1 := by
  have hp := qMode_pos t n
  have hq := qMode_lt_one ht n
  apply (div_lt_one (sq_pos_of_pos (by linarith : 0<1+qMode t n))).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hq)]

theorem coefficient_le {t : ℝ} (n : ℕ) : coefficient t n≤4*qMode t n := by
  have hp := qMode_pos t n
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0<1+qMode t n))).mpr
  have hden : 1≤(1+qMode t n)^2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden (by positivity : 0≤4*qMode t n)]

theorem qMode_summable {t : ℝ} (ht : 0<t) : Summable (qMode t) := by
  have he : ‖Real.exp (-2*t)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    linarith
  apply ((summable_geometric_of_norm_lt_one he).mul_left (Real.exp (-t))).congr
  intro n
  rw [← Real.exp_nat_mul,← Real.exp_add]
  unfold qMode
  congr 1
  ring

theorem coefficient_summable {t : ℝ} (ht : 0<t) : Summable (coefficient t) :=
  ((qMode_summable ht).mul_left 4).of_nonneg_of_le
    (fun n => (coefficient_pos t n).le) coefficient_le

theorem factor_pos {t r : ℝ} (ht : 0<t) (hr : r∈Icc (0:ℝ) 1) (n : ℕ) :
    0<factor t r n := by
  have hp := coefficient_pos t n
  have hlt := coefficient_lt_one ht n
  have hh := mul_le_mul_of_nonneg_left hr.2 hp.le
  unfold factor
  nlinarith

theorem log_summable {t : ℝ} (ht : 0<t) (r : ℝ) :
    Summable (fun n => Real.log (factor t r n)) := by
  convert Real.summable_log_one_add_of_summable ((coefficient_summable ht).mul_right (-r)) using 1
  ext n
  congr 1
  unfold factor
  ring

theorem product_eq_exp {t r : ℝ} (ht : 0<t) (hr : r∈Icc (0:ℝ) 1) :
    jacobiProduct t r=Real.exp (logProduct t r) :=
  (Real.rexp_tsum_eq_tprod (factor_pos ht hr) (log_summable ht r)).symm

theorem product_pos {t r : ℝ} (ht : 0<t) (hr : r∈Icc (0:ℝ) 1) :
    0<jacobiProduct t r := by rw [product_eq_exp ht hr]; exact Real.exp_pos _

/-- Infinite-product Jensen is justified by convergence of the real logarithms. -/
theorem logProduct_concave {t : ℝ} (ht : 0<t) :
    ConcaveOn ℝ (Icc (0:ℝ) 1) (logProduct t) := by
  refine ⟨convex_Icc 0 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a*x+b*y∈Icc (0:ℝ) 1 := (convex_Icc (0:ℝ) 1) hx hy ha hb hab
  have hn (n : ℕ) : a*Real.log (factor t x n)+b*Real.log (factor t y n)≤
      Real.log (factor t (a*x+b*y) n) := by
    have hh := strictConcaveOn_log_Ioi.concaveOn.2 (factor_pos ht hx n) (factor_pos ht hy n) ha hb hab
    have he : factor t (a*x+b*y) n=a*factor t x n+b*factor t y n := by
      unfold factor
      nlinarith [hab]
    simpa only [smul_eq_mul,he] using hh
  have hh := ((log_summable ht x).mul_left a |>.add ((log_summable ht y).mul_left b)).tsum_le_tsum hn
    (log_summable ht (a*x+b*y))
  rw [((log_summable ht x).mul_left a).tsum_add ((log_summable ht y).mul_left b),
    tsum_mul_left,tsum_mul_left] at hh
  exact hh

theorem logProduct_antitone {t : ℝ} (ht : 0<t) :
    AntitoneOn (logProduct t) (Icc (0:ℝ) 1) := by
  intro r hr s hs hrs
  apply (log_summable ht s).tsum_le_tsum _ (log_summable ht r)
  intro n
  apply Real.log_le_log (factor_pos ht hs n)
  unfold factor
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hrs (coefficient_pos t n).le) _

theorem product_antitone {t : ℝ} (ht : 0<t) :
    AntitoneOn (jacobiProduct t) (Icc (0:ℝ) 1) := by
  intro r hr s hs hrs
  rw [product_eq_exp ht hr,product_eq_exp ht hs]
  exact Real.exp_le_exp.mpr (logProduct_antitone ht hr hs hrs)

theorem average_mem {d : ℕ} (hd : 0<d) (r : Fin d → ℝ) (hr : ∀ i,r i∈Icc (0:ℝ) 1) :
    (∑ i,r i)/(d:ℝ)∈Icc (0:ℝ) 1 := by
  have hp : (0:ℝ)<d := Nat.cast_pos.mpr hd
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => (hr i).1)) hp.le,(div_le_one hp).mpr ?_⟩
  simpa using Finset.sum_le_sum (s := Finset.univ) (f := r) (g := fun _ => (1:ℝ)) (fun i _ => (hr i).2)

/-- Exact diagonal comparison for the convergent normalized Jacobi product. -/
theorem product_diagonal {d : ℕ} (hd : 0<d) {t : ℝ} (ht : 0<t)
    (r : Fin d → ℝ) (hr : ∀ i,r i∈Icc (0:ℝ) 1) :
    (∏ i,jacobiProduct t (r i))≤jacobiProduct t ((∑ i,r i)/(d:ℝ))^d := by
  have hp : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hJ := (logProduct_concave ht).le_map_sum (t := Finset.univ)
    (w := fun _ : Fin d => 1/(d:ℝ)) (p := r)
    (fun _ _ => by positivity) (by simp [hp.ne']) (fun i _ => hr i)
  simp only [smul_eq_mul,← Finset.mul_sum,one_div] at hJ
  have hJ' : (∑ i,logProduct t (r i))≤(d:ℝ)*logProduct t ((∑ i,r i)/(d:ℝ)) := by
    have hh : (∑ i,logProduct t (r i))/(d:ℝ)≤logProduct t ((∑ i,r i)/(d:ℝ)) := by
      simpa only [div_eq_mul_inv,mul_comm] using hJ
    exact (div_le_iff₀ hp).mp hh |>.trans_eq (mul_comm _ _)
  simp_rw [product_eq_exp ht (hr _)]
  rw [product_eq_exp ht (average_mem hd r hr),← Real.exp_sum,← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hJ'

#print axioms product_eq_exp
#print axioms logProduct_concave
#print axioms product_diagonal
end BecknerOnofri.HighDim.SpatialThetaProduct
