import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0021
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0021
open CandidateBatch0021 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0336 : AffinePiece := pieces[296]'(by decide +kernel)
theorem intervalAccepted0336 : candidateIntervalCheck candidate0336 (1237/10000) (1239/10000) piece0336=true := by decide +kernel
noncomputable def cell0336 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0336 accepted0336 (1237/10000) (1239/10000) piece0336
    intervalAccepted0336 (fun t => piece_le_psi ⟨296,by decide +kernel⟩ t)
def piece0337 : AffinePiece := pieces[297]'(by decide +kernel)
theorem intervalAccepted0337 : candidateIntervalCheck candidate0337 (1239/10000) (1241/10000) piece0337=true := by decide +kernel
noncomputable def cell0337 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0337 accepted0337 (1239/10000) (1241/10000) piece0337
    intervalAccepted0337 (fun t => piece_le_psi ⟨297,by decide +kernel⟩ t)
def piece0338 : AffinePiece := pieces[298]'(by decide +kernel)
theorem intervalAccepted0338 : candidateIntervalCheck candidate0338 (1241/10000) (1243/10000) piece0338=true := by decide +kernel
noncomputable def cell0338 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0338 accepted0338 (1241/10000) (1243/10000) piece0338
    intervalAccepted0338 (fun t => piece_le_psi ⟨298,by decide +kernel⟩ t)
def piece0339 : AffinePiece := pieces[299]'(by decide +kernel)
theorem intervalAccepted0339 : candidateIntervalCheck candidate0339 (1243/10000) (249/2000) piece0339=true := by decide +kernel
noncomputable def cell0339 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0339 accepted0339 (1243/10000) (249/2000) piece0339
    intervalAccepted0339 (fun t => piece_le_psi ⟨299,by decide +kernel⟩ t)
def piece0340 : AffinePiece := pieces[300]'(by decide +kernel)
theorem intervalAccepted0340 : candidateIntervalCheck candidate0340 (249/2000) (1247/10000) piece0340=true := by decide +kernel
noncomputable def cell0340 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0340 accepted0340 (249/2000) (1247/10000) piece0340
    intervalAccepted0340 (fun t => piece_le_psi ⟨300,by decide +kernel⟩ t)
def piece0341 : AffinePiece := pieces[301]'(by decide +kernel)
theorem intervalAccepted0341 : candidateIntervalCheck candidate0341 (1247/10000) (1249/10000) piece0341=true := by decide +kernel
noncomputable def cell0341 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0341 accepted0341 (1247/10000) (1249/10000) piece0341
    intervalAccepted0341 (fun t => piece_le_psi ⟨301,by decide +kernel⟩ t)
def piece0342 : AffinePiece := pieces[302]'(by decide +kernel)
theorem intervalAccepted0342 : candidateIntervalCheck candidate0342 (1249/10000) (1251/10000) piece0342=true := by decide +kernel
noncomputable def cell0342 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0342 accepted0342 (1249/10000) (1251/10000) piece0342
    intervalAccepted0342 (fun t => piece_le_psi ⟨302,by decide +kernel⟩ t)
def piece0343 : AffinePiece := pieces[303]'(by decide +kernel)
theorem intervalAccepted0343 : candidateIntervalCheck candidate0343 (1251/10000) (1253/10000) piece0343=true := by decide +kernel
noncomputable def cell0343 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0343 accepted0343 (1251/10000) (1253/10000) piece0343
    intervalAccepted0343 (fun t => piece_le_psi ⟨303,by decide +kernel⟩ t)
def piece0344 : AffinePiece := pieces[304]'(by decide +kernel)
theorem intervalAccepted0344 : candidateIntervalCheck candidate0344 (1253/10000) (251/2000) piece0344=true := by decide +kernel
noncomputable def cell0344 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0344 accepted0344 (1253/10000) (251/2000) piece0344
    intervalAccepted0344 (fun t => piece_le_psi ⟨304,by decide +kernel⟩ t)
def piece0345 : AffinePiece := pieces[305]'(by decide +kernel)
theorem intervalAccepted0345 : candidateIntervalCheck candidate0345 (251/2000) (1257/10000) piece0345=true := by decide +kernel
noncomputable def cell0345 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0345 accepted0345 (251/2000) (1257/10000) piece0345
    intervalAccepted0345 (fun t => piece_le_psi ⟨305,by decide +kernel⟩ t)
def piece0346 : AffinePiece := pieces[306]'(by decide +kernel)
theorem intervalAccepted0346 : candidateIntervalCheck candidate0346 (1257/10000) (1259/10000) piece0346=true := by decide +kernel
noncomputable def cell0346 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0346 accepted0346 (1257/10000) (1259/10000) piece0346
    intervalAccepted0346 (fun t => piece_le_psi ⟨306,by decide +kernel⟩ t)
def piece0347 : AffinePiece := pieces[307]'(by decide +kernel)
theorem intervalAccepted0347 : candidateIntervalCheck candidate0347 (1259/10000) (1261/10000) piece0347=true := by decide +kernel
noncomputable def cell0347 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0347 accepted0347 (1259/10000) (1261/10000) piece0347
    intervalAccepted0347 (fun t => piece_le_psi ⟨307,by decide +kernel⟩ t)
def piece0348 : AffinePiece := pieces[308]'(by decide +kernel)
theorem intervalAccepted0348 : candidateIntervalCheck candidate0348 (1261/10000) (1263/10000) piece0348=true := by decide +kernel
noncomputable def cell0348 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0348 accepted0348 (1261/10000) (1263/10000) piece0348
    intervalAccepted0348 (fun t => piece_le_psi ⟨308,by decide +kernel⟩ t)
def piece0349 : AffinePiece := pieces[309]'(by decide +kernel)
theorem intervalAccepted0349 : candidateIntervalCheck candidate0349 (1263/10000) (253/2000) piece0349=true := by decide +kernel
noncomputable def cell0349 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0349 accepted0349 (1263/10000) (253/2000) piece0349
    intervalAccepted0349 (fun t => piece_le_psi ⟨309,by decide +kernel⟩ t)
def piece0350 : AffinePiece := pieces[310]'(by decide +kernel)
theorem intervalAccepted0350 : candidateIntervalCheck candidate0350 (253/2000) (1267/10000) piece0350=true := by decide +kernel
noncomputable def cell0350 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0350 accepted0350 (253/2000) (1267/10000) piece0350
    intervalAccepted0350 (fun t => piece_le_psi ⟨310,by decide +kernel⟩ t)
def piece0351 : AffinePiece := pieces[311]'(by decide +kernel)
theorem intervalAccepted0351 : candidateIntervalCheck candidate0351 (1267/10000) (1269/10000) piece0351=true := by decide +kernel
noncomputable def cell0351 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0351 accepted0351 (1267/10000) (1269/10000) piece0351
    intervalAccepted0351 (fun t => piece_le_psi ⟨311,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0336, cell0337, cell0338, cell0339, cell0340, cell0341, cell0342, cell0343, cell0344, cell0345, cell0346, cell0347, cell0348, cell0349, cell0350, cell0351]
theorem chainAccepted : spinCellChainCheck (1237/10000) (1269/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1237/10000) (1269/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0021
