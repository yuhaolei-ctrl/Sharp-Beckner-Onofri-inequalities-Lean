module

public import BecknerOnofri.CircleGammaPsiWeights
public import BecknerOnofri.CircleGammaPsiEntropy

@[expose] public section

/-! Step 5 of the proof of Lemma 5.17 (`lem:section5-global-small-gamma`):
the finite Bernstein certificates. The numerators are assembled by the kernel
from the small polynomials of Steps 1–3, so no large coefficient table is
stored. Here `A = 157/500`, `c = 67/100`, `D = 6-t`, and the denominator of
`A + B` is `3A·(3x²-12x+10) + c(15-8x)`.

* `smallNum` (degree 7 in `x`) is the numerator of `g₀ = E + AB/(A+B)`;
  positive on `[0,9/16]`.
* `zNumReduced` (degree 23 in `t`) is the numerator of `z`; positive on
  `[3/4,1]`.
* `largeNum` (degree 62 in `t`) is a numerator of `g₁`; positive on
  `[3/4,17/20]` and `[17/20,1]`. It differs from the reduced degree-58
  numerator of the manuscript by a factor that is positive on `[3/4,1]`. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar
open GammaPoly

/-- The denominator of `A + B(x)`, up to the factor `3(3x²-12x+10)`. -/
def minDen : List ℚ := add (smul (3 * (157/500)) weightDenOne) (smul (67/100) weightNumOne)
def smallNum : List ℚ :=
  add (smul (-1) (mul entropyNum minDen))
    (smul (1441440000 * (157/500) * (67/100)) (mul entropyDen weightNumOne))
def barrierT : List ℚ := subsq barrierCoeffs
def sideD : List ℚ := [6, -1]
/-- `t³ P² L_*/x` written as a polynomial in `t`. -/
def lowerNum : List ℚ :=
  add (add (mul (mul sideD [0, 1]) (mul barrierT barrierT))
      (mul (mul [2, -6] [1, 0, -1]) barrierT))
    (smul (-2) (mul [1, 0, -1] [1, 0, -1]))
def zNum : List ℚ :=
  sub (mul lowerNum (subsq minDen))
    (smul (67/100)
      (mul (mul sideD (subsq weightNumOne)) (mul [0, 0, 0, 1] (mul barrierT barrierT))))
def zNumReduced : List ℚ := zNum.drop 3
def kDen : List ℚ :=
  add (smul 12 (mul (subsq minDen) (subsq weightDenTwo)))
    (smul (15 * (67/100)) (mul (mul (subsq weightNumTwo) (mul sideD sideD)) (subsq weightDenOne)))
def largeNum : List ℚ :=
  add (mul (mul (subsq smallNum) kDen) (npow barrierT 4))
    (smul (5 * (67/100) * 1441440000)
      (mul (mul (subsq entropyDen) (subsq weightNumTwo)) (mul zNumReduced zNumReduced)))

theorem minDen_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < eval minDen x :=
  pos_of_posCheck (lo := 0) (hi := 1) (by decide +kernel) (by simpa using h0) (by simpa using h1)

/-- 8 Bernstein coefficients: `N₀ > 0` on `[0,9/16]`. -/
theorem smallNum_pos {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 9/16) : 0 < eval smallNum x :=
  pos_of_posCheck (lo := 0) (hi := 9/16) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem zNum_eq (t : ℝ) : eval zNum t = t^3 * eval zNumReduced t :=
  eval_drop 3 zNum (by decide +kernel) t

/-- 24 Bernstein coefficients: `N_z > 0` on `[3/4,1]`. -/
theorem zNumReduced_pos {t : ℝ} (h0 : 3/4 ≤ t) (h1 : t ≤ 1) : 0 < eval zNumReduced t :=
  pos_of_posCheck (lo := 3/4) (hi := 1) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem kDen_pos {t : ℝ} (h0 : 3/4 ≤ t) (h1 : t ≤ 1) : 0 < eval kDen t :=
  pos_of_posCheck (lo := 3/4) (hi := 1) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem largeNum_left_pos {t : ℝ} (h0 : 3/4 ≤ t) (h1 : t ≤ 17/20) : 0 < eval largeNum t :=
  pos_of_posCheck (lo := 3/4) (hi := 17/20) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

theorem largeNum_right_pos {t : ℝ} (h0 : 17/20 ≤ t) (h1 : t ≤ 1) : 0 < eval largeNum t :=
  pos_of_posCheck (lo := 17/20) (hi := 1) (by decide +kernel) (by simpa using h0)
    (by simpa using h1)

/-- 126 Bernstein coefficients: `N₁ > 0` on `[3/4,1]`. -/
theorem largeNum_pos {t : ℝ} (h0 : 3/4 ≤ t) (h1 : t ≤ 1) : 0 < eval largeNum t := by
  rcases le_total t (17/20) with h | h
  · exact largeNum_left_pos h0 h
  · exact largeNum_right_pos h h1

end BecknerOnofri.HighDim.CircleScalar
