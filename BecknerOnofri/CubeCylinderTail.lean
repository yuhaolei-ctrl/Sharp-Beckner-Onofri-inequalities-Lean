module

public import BecknerOnofri.CubeTransverseSlice

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Classical
open scoped BigOperators
namespace BecknerOnofri.HighDim.CubeLatticeTail
open Legacy.TorusEndpoint.GreenMultiplierSummability

def cylinderBound (p : ℝ) (m N : ℕ) : ℝ :=
  ∑j∈Finset.range (m+1), (m.choose j:ℝ)*Real.pi^((j:ℝ)/2)*
    Real.Gamma (p-(j:ℝ)/2)/Real.Gamma p *
      ((N:ℝ)^((j:ℝ)-2*p)+(N:ℝ)^((j:ℝ)-2*p+1)/(2*p-(j:ℝ)-1))

theorem power_tail_summable {a : ℝ} (ha : a < -1) (N : ℕ) (hN : 0<N) :
    Summable (fun n : ℕ => ((n+N:ℕ):ℝ)^a) := by
  have hN0 : (0:ℝ)<N := by exact_mod_cast hN
  have hanti : AntitoneOn (fun x : ℝ => x^a) (Ici (N:ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hN0.trans_le hx) hxy (by linarith)
  exact (summable_nat_add_iff N).mpr (hanti.summable_of_integrableOn_Ioi
    (integrableOn_Ioi_rpow_of_lt ha hN0)
    (by intro x hx; exact Real.rpow_nonneg (hN0.trans hx).le _))

theorem sliceBound_summable {p : ℝ} {m N : ℕ} (hp : ((m:ℝ)+1)/2<p) (hN : 0<N) :
    Summable (fun n : ℕ => sliceBound p m ((n+N:ℕ):ℝ)) := by
  unfold sliceBound
  apply summable_sum
  intro j hj
  apply Summable.mul_left
  apply power_tail_summable _ N hN
  have hjm : (j:ℝ)≤m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  linarith

theorem sliceBound_sum_le {p : ℝ} {m N : ℕ} (hp : ((m:ℝ)+1)/2<p) (hN : 0<N) :
    (∑' n : ℕ,sliceBound p m ((n+N:ℕ):ℝ)) ≤ cylinderBound p m N := by
  unfold sliceBound cylinderBound
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_le_sum
    intro j hj
    have hjm : (j:ℝ)≤m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    have hpow : (j:ℝ)-2*p< -1 := by linarith
    rw [tsum_mul_left]
    have hc : 0≤(m.choose j:ℝ)*Real.pi^((j:ℝ)/2)*Real.Gamma (p-(j:ℝ)/2)/Real.Gamma p := by
      apply div_nonneg
      · exact mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by linarith)).le
      · exact (Real.Gamma_pos_of_pos (by have : (0:ℝ)≤m := Nat.cast_nonneg m; linarith)).le
    have h := mul_le_mul_of_nonneg_left (power_tail_le hpow N hN) hc
    convert h using 1 <;> congr 2 <;> ring
  · intro j hj
    apply Summable.mul_left
    apply power_tail_summable _ N hN
    have hjm : (j:ℝ)≤m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    linarith

def cylinderWeight (p : ℝ) (m N : ℕ) (v : ℕ × (Fin m → ℤ)) : ℝ :=
  sliceWeight p ((v.1+N:ℕ):ℝ) v.2

theorem cylinder_summable {p : ℝ} {m N : ℕ} (hp : ((m:ℝ)+1)/2<p) (hN : 0<N) :
    Summable (cylinderWeight p m N) := by
  have hn (n : ℕ) : (0:ℝ)<((n+N:ℕ):ℝ) := by positivity
  have hp' : (m:ℝ)/2<p := by linarith
  apply (summable_prod_of_nonneg (f := cylinderWeight p m N) (fun v=>Real.rpow_nonneg
    (add_nonneg (sq_nonneg _) (radiusSq_nonneg v.2)) _)).mpr
  constructor
  · intro n
    change Summable (sliceWeight p ((n+N:ℕ):ℝ) : (Fin m→ℤ)→ℝ)
    exact slice_summable (m:=m) (p:=p) (a:=((n+N:ℕ):ℝ)) hp' (hn n)
  · change Summable (fun n : ℕ=>∑'k : Fin m→ℤ,sliceWeight p ((n+N:ℕ):ℝ) k)
    exact (sliceBound_summable (m:=m) (p:=p) (N:=N) hp hN).of_nonneg_of_le
      (fun n=>tsum_nonneg (fun k=>Real.rpow_nonneg
        (add_nonneg (sq_nonneg _) (radiusSq_nonneg k)) _))
      (fun n=>slice_tsum_le (m:=m) (p:=p) (a:=((n+N:ℕ):ℝ)) hp' (hn n))

/-- Explicit gamma estimate on each one-sided coordinate cylinder. -/
theorem cylinder_tsum_le {p : ℝ} {m N : ℕ} (hp : ((m:ℝ)+1)/2<p) (hN : 0<N) :
    (∑'v,cylinderWeight p m N v) ≤ cylinderBound p m N := by
  have hn (n : ℕ) : (0:ℝ)<((n+N:ℕ):ℝ) := by positivity
  have hp' : (m:ℝ)/2<p := by linarith
  have hinner : ∀n : ℕ, Summable (fun k=>cylinderWeight p m N (n,k)) :=
    fun n=>by
      change Summable (sliceWeight p ((n+N:ℕ):ℝ) : (Fin m→ℤ)→ℝ)
      exact slice_summable (m:=m) (p:=p) (a:=((n+N:ℕ):ℝ)) hp' (hn n)
  rw [(cylinder_summable (m:=m) (p:=p) (N:=N) hp hN).tsum_prod' hinner]
  change (∑'n : ℕ,∑'k : Fin m→ℤ,sliceWeight p ((n+N:ℕ):ℝ) k)≤_
  have houter : Summable (fun n : ℕ=>∑'k : Fin m→ℤ,sliceWeight p ((n+N:ℕ):ℝ) k) :=
    (cylinder_summable (m:=m) (p:=p) (N:=N) hp hN).prod
  exact (houter.tsum_le_tsum
    (fun n=>slice_tsum_le (m:=m) (p:=p) (a:=((n+N:ℕ):ℝ)) hp' (hn n)) (sliceBound_summable (m:=m) (p:=p) (N:=N) hp hN)).trans
      (sliceBound_sum_le (m:=m) (p:=p) (N:=N) hp hN)

#print axioms cylinder_tsum_le
end BecknerOnofri.HighDim.CubeLatticeTail
