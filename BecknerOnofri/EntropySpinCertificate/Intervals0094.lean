import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0094
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0094
open CandidateBatch0094 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1504 : AffinePiece := pieces[1262]'(by decide +kernel)
theorem intervalAccepted1504 : candidateIntervalCheck candidate1504 (4213/5000) (8427/10000) piece1504=true := by decide +kernel
noncomputable def cell1504 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1504 accepted1504 (4213/5000) (8427/10000) piece1504
    intervalAccepted1504 (fun t => piece_le_psi ⟨1262,by decide +kernel⟩ t)
def piece1505 : AffinePiece := pieces[1263]'(by decide +kernel)
theorem intervalAccepted1505 : candidateIntervalCheck candidate1505 (8427/10000) (2107/2500) piece1505=true := by decide +kernel
noncomputable def cell1505 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1505 accepted1505 (8427/10000) (2107/2500) piece1505
    intervalAccepted1505 (fun t => piece_le_psi ⟨1263,by decide +kernel⟩ t)
def piece1506 : AffinePiece := pieces[1264]'(by decide +kernel)
theorem intervalAccepted1506 : candidateIntervalCheck candidate1506 (2107/2500) (8429/10000) piece1506=true := by decide +kernel
noncomputable def cell1506 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1506 accepted1506 (2107/2500) (8429/10000) piece1506
    intervalAccepted1506 (fun t => piece_le_psi ⟨1264,by decide +kernel⟩ t)
def piece1507 : AffinePiece := pieces[1265]'(by decide +kernel)
theorem intervalAccepted1507 : candidateIntervalCheck candidate1507 (8429/10000) (843/1000) piece1507=true := by decide +kernel
noncomputable def cell1507 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1507 accepted1507 (8429/10000) (843/1000) piece1507
    intervalAccepted1507 (fun t => piece_le_psi ⟨1265,by decide +kernel⟩ t)
def piece1508 : AffinePiece := pieces[1266]'(by decide +kernel)
theorem intervalAccepted1508 : candidateIntervalCheck candidate1508 (843/1000) (8431/10000) piece1508=true := by decide +kernel
noncomputable def cell1508 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1508 accepted1508 (843/1000) (8431/10000) piece1508
    intervalAccepted1508 (fun t => piece_le_psi ⟨1266,by decide +kernel⟩ t)
def piece1509 : AffinePiece := pieces[1267]'(by decide +kernel)
theorem intervalAccepted1509 : candidateIntervalCheck candidate1509 (8431/10000) (527/625) piece1509=true := by decide +kernel
noncomputable def cell1509 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1509 accepted1509 (8431/10000) (527/625) piece1509
    intervalAccepted1509 (fun t => piece_le_psi ⟨1267,by decide +kernel⟩ t)
def piece1510 : AffinePiece := pieces[1268]'(by decide +kernel)
theorem intervalAccepted1510 : candidateIntervalCheck candidate1510 (527/625) (8433/10000) piece1510=true := by decide +kernel
noncomputable def cell1510 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1510 accepted1510 (527/625) (8433/10000) piece1510
    intervalAccepted1510 (fun t => piece_le_psi ⟨1268,by decide +kernel⟩ t)
def piece1511 : AffinePiece := pieces[1269]'(by decide +kernel)
theorem intervalAccepted1511 : candidateIntervalCheck candidate1511 (8433/10000) (4217/5000) piece1511=true := by decide +kernel
noncomputable def cell1511 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1511 accepted1511 (8433/10000) (4217/5000) piece1511
    intervalAccepted1511 (fun t => piece_le_psi ⟨1269,by decide +kernel⟩ t)
def piece1512 : AffinePiece := pieces[1270]'(by decide +kernel)
theorem intervalAccepted1512 : candidateIntervalCheck candidate1512 (4217/5000) (1687/2000) piece1512=true := by decide +kernel
noncomputable def cell1512 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1512 accepted1512 (4217/5000) (1687/2000) piece1512
    intervalAccepted1512 (fun t => piece_le_psi ⟨1270,by decide +kernel⟩ t)
def piece1513 : AffinePiece := pieces[1271]'(by decide +kernel)
theorem intervalAccepted1513 : candidateIntervalCheck candidate1513 (1687/2000) (2109/2500) piece1513=true := by decide +kernel
noncomputable def cell1513 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1513 accepted1513 (1687/2000) (2109/2500) piece1513
    intervalAccepted1513 (fun t => piece_le_psi ⟨1271,by decide +kernel⟩ t)
def piece1514 : AffinePiece := pieces[1272]'(by decide +kernel)
theorem intervalAccepted1514 : candidateIntervalCheck candidate1514 (2109/2500) (8437/10000) piece1514=true := by decide +kernel
noncomputable def cell1514 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1514 accepted1514 (2109/2500) (8437/10000) piece1514
    intervalAccepted1514 (fun t => piece_le_psi ⟨1272,by decide +kernel⟩ t)
def piece1515 : AffinePiece := pieces[1273]'(by decide +kernel)
theorem intervalAccepted1515 : candidateIntervalCheck candidate1515 (8437/10000) (4219/5000) piece1515=true := by decide +kernel
noncomputable def cell1515 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1515 accepted1515 (8437/10000) (4219/5000) piece1515
    intervalAccepted1515 (fun t => piece_le_psi ⟨1273,by decide +kernel⟩ t)
def piece1516 : AffinePiece := pieces[1274]'(by decide +kernel)
theorem intervalAccepted1516 : candidateIntervalCheck candidate1516 (4219/5000) (8439/10000) piece1516=true := by decide +kernel
noncomputable def cell1516 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1516 accepted1516 (4219/5000) (8439/10000) piece1516
    intervalAccepted1516 (fun t => piece_le_psi ⟨1274,by decide +kernel⟩ t)
def piece1517 : AffinePiece := pieces[1275]'(by decide +kernel)
theorem intervalAccepted1517 : candidateIntervalCheck candidate1517 (8439/10000) (211/250) piece1517=true := by decide +kernel
noncomputable def cell1517 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1517 accepted1517 (8439/10000) (211/250) piece1517
    intervalAccepted1517 (fun t => piece_le_psi ⟨1275,by decide +kernel⟩ t)
def piece1518 : AffinePiece := pieces[1276]'(by decide +kernel)
theorem intervalAccepted1518 : candidateIntervalCheck candidate1518 (211/250) (8441/10000) piece1518=true := by decide +kernel
noncomputable def cell1518 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1518 accepted1518 (211/250) (8441/10000) piece1518
    intervalAccepted1518 (fun t => piece_le_psi ⟨1276,by decide +kernel⟩ t)
def piece1519 : AffinePiece := pieces[1277]'(by decide +kernel)
theorem intervalAccepted1519 : candidateIntervalCheck candidate1519 (8441/10000) (4221/5000) piece1519=true := by decide +kernel
noncomputable def cell1519 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1519 accepted1519 (8441/10000) (4221/5000) piece1519
    intervalAccepted1519 (fun t => piece_le_psi ⟨1277,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1504, cell1505, cell1506, cell1507, cell1508, cell1509, cell1510, cell1511, cell1512, cell1513, cell1514, cell1515, cell1516, cell1517, cell1518, cell1519]
theorem chainAccepted : spinCellChainCheck (4213/5000) (4221/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4213/5000) (4221/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0094
