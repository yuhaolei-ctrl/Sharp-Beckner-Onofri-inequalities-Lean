module

public import BecknerOnofri.ScalarBesselRounded
public import BecknerOnofri.EntropyExpInteger

@[expose] public section

namespace BecknerOnofri.HighDim.ScalarCertificate
open EntropyTail.ExpCertificate

structure IntegerBesselState where
  termLower : ℤ
  termUpper : ℤ
  sumLower : ℤ
  sumUpper : ℤ

def IntegerBesselState.rational (P : ℕ) (c : IntegerBesselState) : BesselState :=
  ⟨(c.termLower : ℚ)/P,(c.termUpper : ℚ)/P,(c.sumLower : ℚ)/P,(c.sumUpper : ℚ)/P⟩

def integerBesselInitial (P : ℕ) (q D : ℤ) (n : ℕ) : IntegerBesselState :=
  let d : ℤ := D^n*n.factorial
  ⟨(P*q^n)/d,ceilDiv (P*q^n) d,0,0⟩

def integerBesselStep (q D : ℤ) (n j : ℕ) (c : IntegerBesselState) : IntegerBesselState :=
  let d : ℤ := D^2*(j+1)*(j+n+1)
  ⟨(q^2*c.termLower)/d,ceilDiv (q^2*c.termUpper) d,
    c.sumLower+c.termLower,c.sumUpper+c.termUpper⟩

def integerBessel (P : ℕ) (q D : ℤ) (n : ℕ) : ℕ → IntegerBesselState
  | 0 => integerBesselInitial P q D n
  | j+1 => integerBesselStep q D n j (integerBessel P q D n j)

theorem integerBesselInitial_eq (P : ℕ) (hP : 0<P) (q D : ℤ) (hD : 0<D) (n : ℕ) :
    (integerBesselInitial P q D n).rational P=besselInitial P ((q : ℚ)/D) n := by
  let d : ℤ := D^n*n.factorial
  have hd : 0<d := by dsimp [d]; positivity
  have hp : (P : ℚ)≠0 := by exact_mod_cast hP.ne'
  have hDq : (D : ℚ)≠0 := by exact_mod_cast hD.ne'
  have he : ((q : ℚ)/D)^n/(n.factorial : ℚ)=
      ((P*q^n : ℤ) : ℚ)/((d : ℚ)*P) := by
    dsimp [d]
    push_cast
    rw [div_pow]
    field_simp
  unfold integerBesselInitial IntegerBesselState.rational besselInitial
  rw [he,roundDown_ratio P hP _ d hd,roundUp_ratio P hP _ d hd]
  simp [d]

theorem integerBesselStep_eq (P : ℕ) (hP : 0<P) (q D : ℤ) (hD : 0<D)
    (n j : ℕ) (c : IntegerBesselState) :
    (integerBesselStep q D n j c).rational P=
      besselStep P ((q : ℚ)/D) n j (c.rational P) := by
  let d : ℤ := D^2*(j+1)*(j+n+1)
  have hd : 0<d := by dsimp [d]; positivity
  have hp : (P : ℚ)≠0 := by exact_mod_cast hP.ne'
  have hDq : (D : ℚ)≠0 := by exact_mod_cast hD.ne'
  have he (a : ℤ) : (((q : ℚ)/D)^2/((j+1 : ℚ)*(j+n+1 : ℚ)))*((a : ℚ)/P)=
      ((q^2*a : ℤ) : ℚ)/((d : ℚ)*P) := by
    dsimp [d]
    push_cast
    field_simp
    <;> ring
  unfold integerBesselStep IntegerBesselState.rational besselStep
  dsimp only
  rw [he,he,roundDown_ratio P hP _ d hd,roundUp_ratio P hP _ d hd]
  simp only [Int.cast_add,add_div]
  rfl

theorem integerBessel_eq (P : ℕ) (hP : 0<P) (q D : ℤ) (hD : 0<D) (n N : ℕ) :
    (integerBessel P q D n N).rational P=besselRounded P ((q : ℚ)/D) n N := by
  induction N with
  | zero => exact integerBesselInitial_eq P hP q D hD n
  | succ N ih =>
    rw [integerBessel,integerBesselStep_eq P hP q D hD,ih,besselRounded]

#print axioms integerBessel_eq
end BecknerOnofri.HighDim.ScalarCertificate
