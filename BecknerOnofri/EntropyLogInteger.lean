import BecknerOnofri.EntropyLogHorner
import BecknerOnofri.EntropyExpInteger

namespace BecknerOnofri.HighDim.EntropyLogCertificate
open EntropyTail.ExpCertificate

def integerHornerStep (P : ℕ) (q D : ℤ) (n : ℕ) (c : ℤ × ℤ) : ℤ × ℤ :=
  let m : ℤ := 2*n+1
  let d := D^2*m
  ((D^2*P+m*q^2*c.1)/d, ceilDiv (D^2*P+m*q^2*c.2) d)

def integerHorner (P : ℕ) (q D : ℤ) (n : ℕ) : ℕ → ℤ × ℤ
  | 0 => (0,0)
  | r+1 => integerHornerStep P q D n (integerHorner P q D (n+1) r)

theorem integerHornerStep_eq (P : ℕ) (hP : 0<P) (q D : ℤ) (hD : 0<D)
    (n : ℕ) (c : ℤ × ℤ) :
    ratPair P (integerHornerStep P q D n c) =
      (roundDown P (1/(2*n+1 : ℚ)+((q : ℚ)/D)^2*(ratPair P c).1),
       roundUp P (1/(2*n+1 : ℚ)+((q : ℚ)/D)^2*(ratPair P c).2)) := by
  let m : ℤ := 2*n+1
  have hm : 0<m := by dsimp [m]; omega
  have hd : 0<D^2*m := mul_pos (sq_pos_of_pos hD) hm
  have hp : (P : ℚ)≠0 := by exact_mod_cast hP.ne'
  have hDq : (D : ℚ)≠0 := by exact_mod_cast hD.ne'
  have hmq : (m : ℚ)≠0 := by exact_mod_cast hm.ne'
  have he (a : ℤ) : 1/(2*n+1 : ℚ)+((q : ℚ)/D)^2*((a : ℚ)/P)=
      ((D^2*P+m*q^2*a : ℤ) : ℚ)/(((D^2*m : ℤ) : ℚ)*P) := by
    have hmcast : (m : ℚ)=2*n+1 := by simp [m]
    rw [← hmcast]
    push_cast
    field_simp
    <;> ring
  unfold integerHornerStep ratPair
  dsimp only
  rw [he,he, roundDown_ratio P hP _ (D^2*m) hd,
    roundUp_ratio P hP _ (D^2*m) hd]

theorem integerHorner_eq (P : ℕ) (hP : 0<P) (q D : ℤ) (hD : 0<D)
    (n r : ℕ) : ratPair P (integerHorner P q D n r)=
      hornerBounds P ((q : ℚ)/D) n r := by
  induction r generalizing n with
  | zero => simp [integerHorner, ratPair, hornerBounds]
  | succ r ih =>
    rw [integerHorner, integerHornerStep_eq P hP q D hD,
      ih (n+1), hornerBounds]

#print axioms integerHorner_eq
end BecknerOnofri.HighDim.EntropyLogCertificate
