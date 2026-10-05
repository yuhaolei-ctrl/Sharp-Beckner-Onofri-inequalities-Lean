import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0093
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0093
open CandidateBatch0093 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1488 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1488 : candidateIntervalCheck candidate1488 (841/1000) (8411/10000) piece1488=true := by decide +kernel
noncomputable def cell1488 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1488 accepted1488 (841/1000) (8411/10000) piece1488
    intervalAccepted1488 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1489 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1489 : candidateIntervalCheck candidate1489 (8411/10000) (2103/2500) piece1489=true := by decide +kernel
noncomputable def cell1489 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1489 accepted1489 (8411/10000) (2103/2500) piece1489
    intervalAccepted1489 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1490 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1490 : candidateIntervalCheck candidate1490 (2103/2500) (8413/10000) piece1490=true := by decide +kernel
noncomputable def cell1490 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1490 accepted1490 (2103/2500) (8413/10000) piece1490
    intervalAccepted1490 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1491 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1491 : candidateIntervalCheck candidate1491 (8413/10000) (4207/5000) piece1491=true := by decide +kernel
noncomputable def cell1491 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1491 accepted1491 (8413/10000) (4207/5000) piece1491
    intervalAccepted1491 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1492 : AffinePiece := pieces[1250]'(by decide +kernel)
theorem intervalAccepted1492 : candidateIntervalCheck candidate1492 (4207/5000) (1683/2000) piece1492=true := by decide +kernel
noncomputable def cell1492 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1492 accepted1492 (4207/5000) (1683/2000) piece1492
    intervalAccepted1492 (fun t => piece_le_psi ⟨1250,by decide +kernel⟩ t)
def piece1493 : AffinePiece := pieces[1251]'(by decide +kernel)
theorem intervalAccepted1493 : candidateIntervalCheck candidate1493 (1683/2000) (526/625) piece1493=true := by decide +kernel
noncomputable def cell1493 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1493 accepted1493 (1683/2000) (526/625) piece1493
    intervalAccepted1493 (fun t => piece_le_psi ⟨1251,by decide +kernel⟩ t)
def piece1494 : AffinePiece := pieces[1252]'(by decide +kernel)
theorem intervalAccepted1494 : candidateIntervalCheck candidate1494 (526/625) (8417/10000) piece1494=true := by decide +kernel
noncomputable def cell1494 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1494 accepted1494 (526/625) (8417/10000) piece1494
    intervalAccepted1494 (fun t => piece_le_psi ⟨1252,by decide +kernel⟩ t)
def piece1495 : AffinePiece := pieces[1253]'(by decide +kernel)
theorem intervalAccepted1495 : candidateIntervalCheck candidate1495 (8417/10000) (4209/5000) piece1495=true := by decide +kernel
noncomputable def cell1495 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1495 accepted1495 (8417/10000) (4209/5000) piece1495
    intervalAccepted1495 (fun t => piece_le_psi ⟨1253,by decide +kernel⟩ t)
def piece1496 : AffinePiece := pieces[1254]'(by decide +kernel)
theorem intervalAccepted1496 : candidateIntervalCheck candidate1496 (4209/5000) (8419/10000) piece1496=true := by decide +kernel
noncomputable def cell1496 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1496 accepted1496 (4209/5000) (8419/10000) piece1496
    intervalAccepted1496 (fun t => piece_le_psi ⟨1254,by decide +kernel⟩ t)
def piece1497 : AffinePiece := pieces[1255]'(by decide +kernel)
theorem intervalAccepted1497 : candidateIntervalCheck candidate1497 (8419/10000) (421/500) piece1497=true := by decide +kernel
noncomputable def cell1497 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1497 accepted1497 (8419/10000) (421/500) piece1497
    intervalAccepted1497 (fun t => piece_le_psi ⟨1255,by decide +kernel⟩ t)
def piece1498 : AffinePiece := pieces[1256]'(by decide +kernel)
theorem intervalAccepted1498 : candidateIntervalCheck candidate1498 (421/500) (8421/10000) piece1498=true := by decide +kernel
noncomputable def cell1498 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1498 accepted1498 (421/500) (8421/10000) piece1498
    intervalAccepted1498 (fun t => piece_le_psi ⟨1256,by decide +kernel⟩ t)
def piece1499 : AffinePiece := pieces[1257]'(by decide +kernel)
theorem intervalAccepted1499 : candidateIntervalCheck candidate1499 (8421/10000) (4211/5000) piece1499=true := by decide +kernel
noncomputable def cell1499 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1499 accepted1499 (8421/10000) (4211/5000) piece1499
    intervalAccepted1499 (fun t => piece_le_psi ⟨1257,by decide +kernel⟩ t)
def piece1500 : AffinePiece := pieces[1258]'(by decide +kernel)
theorem intervalAccepted1500 : candidateIntervalCheck candidate1500 (4211/5000) (8423/10000) piece1500=true := by decide +kernel
noncomputable def cell1500 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1500 accepted1500 (4211/5000) (8423/10000) piece1500
    intervalAccepted1500 (fun t => piece_le_psi ⟨1258,by decide +kernel⟩ t)
def piece1501 : AffinePiece := pieces[1259]'(by decide +kernel)
theorem intervalAccepted1501 : candidateIntervalCheck candidate1501 (8423/10000) (1053/1250) piece1501=true := by decide +kernel
noncomputable def cell1501 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1501 accepted1501 (8423/10000) (1053/1250) piece1501
    intervalAccepted1501 (fun t => piece_le_psi ⟨1259,by decide +kernel⟩ t)
def piece1502 : AffinePiece := pieces[1260]'(by decide +kernel)
theorem intervalAccepted1502 : candidateIntervalCheck candidate1502 (1053/1250) (337/400) piece1502=true := by decide +kernel
noncomputable def cell1502 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1502 accepted1502 (1053/1250) (337/400) piece1502
    intervalAccepted1502 (fun t => piece_le_psi ⟨1260,by decide +kernel⟩ t)
def piece1503 : AffinePiece := pieces[1261]'(by decide +kernel)
theorem intervalAccepted1503 : candidateIntervalCheck candidate1503 (337/400) (4213/5000) piece1503=true := by decide +kernel
noncomputable def cell1503 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1503 accepted1503 (337/400) (4213/5000) piece1503
    intervalAccepted1503 (fun t => piece_le_psi ⟨1261,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1488, cell1489, cell1490, cell1491, cell1492, cell1493, cell1494, cell1495, cell1496, cell1497, cell1498, cell1499, cell1500, cell1501, cell1502, cell1503]
theorem chainAccepted : spinCellChainCheck (841/1000) (4213/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (841/1000) (4213/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0093
