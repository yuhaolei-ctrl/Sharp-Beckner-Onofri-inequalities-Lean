module

public import BecknerOnofri.CircleGammaPsiPoly

namespace BecknerOnofri.HighDim.CircleScalar.GammaPoly

def pP : List ℚ := [1, -1/2, -1/12, -1/48, -1/10, 49/240]
def nB : List ℚ := [15, -8]
def dB : List ℚ := [10, -12, 3]
def nC : List ℚ := [12, -7]
def dC : List ℚ := [15, -20, 6]
def dE : List ℚ := [30, -40, 11]
def nE : List ℚ := [6882876000, -8276268000, 1454760450, 7405775520, -10154519635, 2826860324]
def dAB : List ℚ := add (smul (3*(157/500)) dB) (smul (67/100) nB)
def N0 : List ℚ := add (smul (-1) (mul nE dAB)) (smul (1441440000*(157/500)*(67/100)) (mul dE nB))
def Pt : List ℚ := subsq pP
def omx : List ℚ := [1, 0, -1]
def dD : List ℚ := [6, -1]
def nL : List ℚ := add (add (mul (mul dD [0,1]) (mul Pt Pt)) (mul (mul [2,-6] omx) Pt))
  (smul (-2) (mul omx omx))
def nz : List ℚ := sub (mul nL (subsq dAB))
  (smul (67/100) (mul (mul dD (subsq nB)) (mul [0,0,0,1] (mul Pt Pt))))
def nzp : List ℚ := nz.drop 3
def dK : List ℚ := add (smul 12 (mul (subsq dAB) (subsq dC)))
  (smul (15*(67/100)) (mul (mul (subsq nC) (mul dD dD)) (subsq dB)))
def N1 : List ℚ := add (mul (mul (subsq N0) dK) (npow Pt 4))
  (smul (5*(67/100)*1441440000) (mul (mul (subsq dE) (subsq nC)) (mul nzp nzp)))

set_option profiler true in
theorem n0_check : posCheck N0 0 (9/16) = true := by decide +kernel
set_option profiler true in
theorem nz_check : posCheck nzp (3/4) 1 = true := by decide +kernel
set_option profiler true in
theorem n1_check : posCheck N1 (3/4) (17/20) = true := by decide +kernel

end BecknerOnofri.HighDim.CircleScalar.GammaPoly
