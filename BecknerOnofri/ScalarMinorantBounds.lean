import BecknerOnofri.EntropyScalarCertificate.Minorant

namespace BecknerOnofri.HighDim.ScalarCertificate
open Set

theorem convexMinorant_le (a e : ℝ) (ps : List AffinePiece) (x U : ℝ)
    (hb : quarticBase a e x≤U) (hp : ∀ p∈ps,p.value x≤U) :
    convexMinorant a e ps x≤U := by
  induction ps with
  | nil => exact hb
  | cons p ps ih =>
    exact max_le (hp p (List.mem_cons_self ..)) (ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)))

namespace CertifiedMinorant

theorem pieces_at_one_check : pieces.all (fun p => decide (p.slope+p.intercept≤(38/125 : ℚ)))=true := by
  decide +kernel

theorem psi_one_upper : psi 1≤38/125 := by
  apply convexMinorant_le
  · norm_num [quarticBase]
  · intro p hp
    have h := of_decide_eq_true (List.all_eq_true.mp pieces_at_one_check p hp)
    have hc := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [AffinePiece.value,mul_one,Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using hc

theorem psi_upper {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) : psi t≤38/125 := by
  have h := psi_convex.2 (show (0 : ℝ)∈univ from trivial) (show (1 : ℝ)∈univ from trivial)
    (sub_nonneg.mpr ht.2) ht.1 (show 1-t+t=1 by ring)
  have hz : psi 0=0 := by simpa using psi_small (x := 0) (by norm_num)
  simp only [smul_eq_mul,mul_zero,mul_one,zero_add,hz,add_zero] at h
  have h1 := mul_le_mul_of_nonneg_left psi_one_upper ht.1
  have h2 := mul_le_mul_of_nonneg_right ht.2 (by norm_num : (0 : ℝ)≤38/125)
  linarith

#print axioms psi_upper
end CertifiedMinorant
end BecknerOnofri.HighDim.ScalarCertificate
