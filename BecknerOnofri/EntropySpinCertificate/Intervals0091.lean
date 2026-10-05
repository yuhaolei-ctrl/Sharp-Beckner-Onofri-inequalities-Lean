import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0091
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0091
open CandidateBatch0091 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1456 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1456 : candidateIntervalCheck candidate1456 (4189/5000) (8379/10000) piece1456=true := by decide +kernel
noncomputable def cell1456 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1456 accepted1456 (4189/5000) (8379/10000) piece1456
    intervalAccepted1456 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1457 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1457 : candidateIntervalCheck candidate1457 (8379/10000) (419/500) piece1457=true := by decide +kernel
noncomputable def cell1457 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1457 accepted1457 (8379/10000) (419/500) piece1457
    intervalAccepted1457 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1458 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1458 : candidateIntervalCheck candidate1458 (419/500) (8381/10000) piece1458=true := by decide +kernel
noncomputable def cell1458 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1458 accepted1458 (419/500) (8381/10000) piece1458
    intervalAccepted1458 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1459 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1459 : candidateIntervalCheck candidate1459 (8381/10000) (4191/5000) piece1459=true := by decide +kernel
noncomputable def cell1459 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1459 accepted1459 (8381/10000) (4191/5000) piece1459
    intervalAccepted1459 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1460 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1460 : candidateIntervalCheck candidate1460 (4191/5000) (8383/10000) piece1460=true := by decide +kernel
noncomputable def cell1460 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1460 accepted1460 (4191/5000) (8383/10000) piece1460
    intervalAccepted1460 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1461 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1461 : candidateIntervalCheck candidate1461 (8383/10000) (524/625) piece1461=true := by decide +kernel
noncomputable def cell1461 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1461 accepted1461 (8383/10000) (524/625) piece1461
    intervalAccepted1461 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1462 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1462 : candidateIntervalCheck candidate1462 (524/625) (1677/2000) piece1462=true := by decide +kernel
noncomputable def cell1462 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1462 accepted1462 (524/625) (1677/2000) piece1462
    intervalAccepted1462 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1463 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1463 : candidateIntervalCheck candidate1463 (1677/2000) (4193/5000) piece1463=true := by decide +kernel
noncomputable def cell1463 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1463 accepted1463 (1677/2000) (4193/5000) piece1463
    intervalAccepted1463 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1464 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1464 : candidateIntervalCheck candidate1464 (4193/5000) (8387/10000) piece1464=true := by decide +kernel
noncomputable def cell1464 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1464 accepted1464 (4193/5000) (8387/10000) piece1464
    intervalAccepted1464 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1465 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1465 : candidateIntervalCheck candidate1465 (8387/10000) (2097/2500) piece1465=true := by decide +kernel
noncomputable def cell1465 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1465 accepted1465 (8387/10000) (2097/2500) piece1465
    intervalAccepted1465 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1466 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1466 : candidateIntervalCheck candidate1466 (2097/2500) (8389/10000) piece1466=true := by decide +kernel
noncomputable def cell1466 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1466 accepted1466 (2097/2500) (8389/10000) piece1466
    intervalAccepted1466 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1467 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1467 : candidateIntervalCheck candidate1467 (8389/10000) (839/1000) piece1467=true := by decide +kernel
noncomputable def cell1467 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1467 accepted1467 (8389/10000) (839/1000) piece1467
    intervalAccepted1467 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1468 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1468 : candidateIntervalCheck candidate1468 (839/1000) (8391/10000) piece1468=true := by decide +kernel
noncomputable def cell1468 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1468 accepted1468 (839/1000) (8391/10000) piece1468
    intervalAccepted1468 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1469 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1469 : candidateIntervalCheck candidate1469 (8391/10000) (1049/1250) piece1469=true := by decide +kernel
noncomputable def cell1469 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1469 accepted1469 (8391/10000) (1049/1250) piece1469
    intervalAccepted1469 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1470 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1470 : candidateIntervalCheck candidate1470 (1049/1250) (8393/10000) piece1470=true := by decide +kernel
noncomputable def cell1470 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1470 accepted1470 (1049/1250) (8393/10000) piece1470
    intervalAccepted1470 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1471 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1471 : candidateIntervalCheck candidate1471 (8393/10000) (4197/5000) piece1471=true := by decide +kernel
noncomputable def cell1471 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1471 accepted1471 (8393/10000) (4197/5000) piece1471
    intervalAccepted1471 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1456, cell1457, cell1458, cell1459, cell1460, cell1461, cell1462, cell1463, cell1464, cell1465, cell1466, cell1467, cell1468, cell1469, cell1470, cell1471]
theorem chainAccepted : spinCellChainCheck (4189/5000) (4197/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4189/5000) (4197/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0091
