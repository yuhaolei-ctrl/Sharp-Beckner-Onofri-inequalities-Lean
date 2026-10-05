module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0025

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0025
open CandidateBatch0025 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0400 : AffinePiece := pieces[360]'(by decide +kernel)
theorem intervalAccepted0400 : candidateIntervalCheck candidate0400 (273/2000) (1367/10000) piece0400=true := by decide +kernel
noncomputable def cell0400 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0400 accepted0400 (273/2000) (1367/10000) piece0400
    intervalAccepted0400 (fun t => piece_le_psi ⟨360,by decide +kernel⟩ t)
def piece0401 : AffinePiece := pieces[361]'(by decide +kernel)
theorem intervalAccepted0401 : candidateIntervalCheck candidate0401 (1367/10000) (1369/10000) piece0401=true := by decide +kernel
noncomputable def cell0401 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0401 accepted0401 (1367/10000) (1369/10000) piece0401
    intervalAccepted0401 (fun t => piece_le_psi ⟨361,by decide +kernel⟩ t)
def piece0402 : AffinePiece := pieces[362]'(by decide +kernel)
theorem intervalAccepted0402 : candidateIntervalCheck candidate0402 (1369/10000) (1371/10000) piece0402=true := by decide +kernel
noncomputable def cell0402 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0402 accepted0402 (1369/10000) (1371/10000) piece0402
    intervalAccepted0402 (fun t => piece_le_psi ⟨362,by decide +kernel⟩ t)
def piece0403 : AffinePiece := pieces[363]'(by decide +kernel)
theorem intervalAccepted0403 : candidateIntervalCheck candidate0403 (1371/10000) (1373/10000) piece0403=true := by decide +kernel
noncomputable def cell0403 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0403 accepted0403 (1371/10000) (1373/10000) piece0403
    intervalAccepted0403 (fun t => piece_le_psi ⟨363,by decide +kernel⟩ t)
def piece0404 : AffinePiece := pieces[364]'(by decide +kernel)
theorem intervalAccepted0404 : candidateIntervalCheck candidate0404 (1373/10000) (11/80) piece0404=true := by decide +kernel
noncomputable def cell0404 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0404 accepted0404 (1373/10000) (11/80) piece0404
    intervalAccepted0404 (fun t => piece_le_psi ⟨364,by decide +kernel⟩ t)
def piece0405 : AffinePiece := pieces[365]'(by decide +kernel)
theorem intervalAccepted0405 : candidateIntervalCheck candidate0405 (11/80) (1377/10000) piece0405=true := by decide +kernel
noncomputable def cell0405 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0405 accepted0405 (11/80) (1377/10000) piece0405
    intervalAccepted0405 (fun t => piece_le_psi ⟨365,by decide +kernel⟩ t)
def piece0406 : AffinePiece := pieces[366]'(by decide +kernel)
theorem intervalAccepted0406 : candidateIntervalCheck candidate0406 (1377/10000) (1379/10000) piece0406=true := by decide +kernel
noncomputable def cell0406 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0406 accepted0406 (1377/10000) (1379/10000) piece0406
    intervalAccepted0406 (fun t => piece_le_psi ⟨366,by decide +kernel⟩ t)
def piece0407 : AffinePiece := pieces[367]'(by decide +kernel)
theorem intervalAccepted0407 : candidateIntervalCheck candidate0407 (1379/10000) (1381/10000) piece0407=true := by decide +kernel
noncomputable def cell0407 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0407 accepted0407 (1379/10000) (1381/10000) piece0407
    intervalAccepted0407 (fun t => piece_le_psi ⟨367,by decide +kernel⟩ t)
def piece0408 : AffinePiece := pieces[368]'(by decide +kernel)
theorem intervalAccepted0408 : candidateIntervalCheck candidate0408 (1381/10000) (1383/10000) piece0408=true := by decide +kernel
noncomputable def cell0408 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0408 accepted0408 (1381/10000) (1383/10000) piece0408
    intervalAccepted0408 (fun t => piece_le_psi ⟨368,by decide +kernel⟩ t)
def piece0409 : AffinePiece := pieces[369]'(by decide +kernel)
theorem intervalAccepted0409 : candidateIntervalCheck candidate0409 (1383/10000) (277/2000) piece0409=true := by decide +kernel
noncomputable def cell0409 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0409 accepted0409 (1383/10000) (277/2000) piece0409
    intervalAccepted0409 (fun t => piece_le_psi ⟨369,by decide +kernel⟩ t)
def piece0410 : AffinePiece := pieces[370]'(by decide +kernel)
theorem intervalAccepted0410 : candidateIntervalCheck candidate0410 (277/2000) (1387/10000) piece0410=true := by decide +kernel
noncomputable def cell0410 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0410 accepted0410 (277/2000) (1387/10000) piece0410
    intervalAccepted0410 (fun t => piece_le_psi ⟨370,by decide +kernel⟩ t)
def piece0411 : AffinePiece := pieces[371]'(by decide +kernel)
theorem intervalAccepted0411 : candidateIntervalCheck candidate0411 (1387/10000) (1389/10000) piece0411=true := by decide +kernel
noncomputable def cell0411 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0411 accepted0411 (1387/10000) (1389/10000) piece0411
    intervalAccepted0411 (fun t => piece_le_psi ⟨371,by decide +kernel⟩ t)
def piece0412 : AffinePiece := pieces[372]'(by decide +kernel)
theorem intervalAccepted0412 : candidateIntervalCheck candidate0412 (1389/10000) (1391/10000) piece0412=true := by decide +kernel
noncomputable def cell0412 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0412 accepted0412 (1389/10000) (1391/10000) piece0412
    intervalAccepted0412 (fun t => piece_le_psi ⟨372,by decide +kernel⟩ t)
def piece0413 : AffinePiece := pieces[373]'(by decide +kernel)
theorem intervalAccepted0413 : candidateIntervalCheck candidate0413 (1391/10000) (1393/10000) piece0413=true := by decide +kernel
noncomputable def cell0413 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0413 accepted0413 (1391/10000) (1393/10000) piece0413
    intervalAccepted0413 (fun t => piece_le_psi ⟨373,by decide +kernel⟩ t)
def piece0414 : AffinePiece := pieces[374]'(by decide +kernel)
theorem intervalAccepted0414 : candidateIntervalCheck candidate0414 (1393/10000) (279/2000) piece0414=true := by decide +kernel
noncomputable def cell0414 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0414 accepted0414 (1393/10000) (279/2000) piece0414
    intervalAccepted0414 (fun t => piece_le_psi ⟨374,by decide +kernel⟩ t)
def piece0415 : AffinePiece := pieces[375]'(by decide +kernel)
theorem intervalAccepted0415 : candidateIntervalCheck candidate0415 (279/2000) (1397/10000) piece0415=true := by decide +kernel
noncomputable def cell0415 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0415 accepted0415 (279/2000) (1397/10000) piece0415
    intervalAccepted0415 (fun t => piece_le_psi ⟨375,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0400, cell0401, cell0402, cell0403, cell0404, cell0405, cell0406, cell0407, cell0408, cell0409, cell0410, cell0411, cell0412, cell0413, cell0414, cell0415]
theorem chainAccepted : spinCellChainCheck (273/2000) (1397/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (273/2000) (1397/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0025
