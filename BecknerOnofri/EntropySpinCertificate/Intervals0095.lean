module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0095

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0095
open CandidateBatch0095 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1520 : AffinePiece := pieces[1278]'(by decide +kernel)
theorem intervalAccepted1520 : candidateIntervalCheck candidate1520 (4221/5000) (8443/10000) piece1520=true := by decide +kernel
noncomputable def cell1520 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1520 accepted1520 (4221/5000) (8443/10000) piece1520
    intervalAccepted1520 (fun t => piece_le_psi ⟨1278,by decide +kernel⟩ t)
def piece1521 : AffinePiece := pieces[1279]'(by decide +kernel)
theorem intervalAccepted1521 : candidateIntervalCheck candidate1521 (8443/10000) (2111/2500) piece1521=true := by decide +kernel
noncomputable def cell1521 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1521 accepted1521 (8443/10000) (2111/2500) piece1521
    intervalAccepted1521 (fun t => piece_le_psi ⟨1279,by decide +kernel⟩ t)
def piece1522 : AffinePiece := pieces[1280]'(by decide +kernel)
theorem intervalAccepted1522 : candidateIntervalCheck candidate1522 (2111/2500) (1689/2000) piece1522=true := by decide +kernel
noncomputable def cell1522 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1522 accepted1522 (2111/2500) (1689/2000) piece1522
    intervalAccepted1522 (fun t => piece_le_psi ⟨1280,by decide +kernel⟩ t)
def piece1523 : AffinePiece := pieces[1281]'(by decide +kernel)
theorem intervalAccepted1523 : candidateIntervalCheck candidate1523 (1689/2000) (4223/5000) piece1523=true := by decide +kernel
noncomputable def cell1523 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1523 accepted1523 (1689/2000) (4223/5000) piece1523
    intervalAccepted1523 (fun t => piece_le_psi ⟨1281,by decide +kernel⟩ t)
def piece1524 : AffinePiece := pieces[1282]'(by decide +kernel)
theorem intervalAccepted1524 : candidateIntervalCheck candidate1524 (4223/5000) (8447/10000) piece1524=true := by decide +kernel
noncomputable def cell1524 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1524 accepted1524 (4223/5000) (8447/10000) piece1524
    intervalAccepted1524 (fun t => piece_le_psi ⟨1282,by decide +kernel⟩ t)
def piece1525 : AffinePiece := pieces[1283]'(by decide +kernel)
theorem intervalAccepted1525 : candidateIntervalCheck candidate1525 (8447/10000) (528/625) piece1525=true := by decide +kernel
noncomputable def cell1525 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1525 accepted1525 (8447/10000) (528/625) piece1525
    intervalAccepted1525 (fun t => piece_le_psi ⟨1283,by decide +kernel⟩ t)
def piece1526 : AffinePiece := pieces[1284]'(by decide +kernel)
theorem intervalAccepted1526 : candidateIntervalCheck candidate1526 (528/625) (8449/10000) piece1526=true := by decide +kernel
noncomputable def cell1526 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1526 accepted1526 (528/625) (8449/10000) piece1526
    intervalAccepted1526 (fun t => piece_le_psi ⟨1284,by decide +kernel⟩ t)
def piece1527 : AffinePiece := pieces[1285]'(by decide +kernel)
theorem intervalAccepted1527 : candidateIntervalCheck candidate1527 (8449/10000) (169/200) piece1527=true := by decide +kernel
noncomputable def cell1527 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1527 accepted1527 (8449/10000) (169/200) piece1527
    intervalAccepted1527 (fun t => piece_le_psi ⟨1285,by decide +kernel⟩ t)
def piece1528 : AffinePiece := pieces[1286]'(by decide +kernel)
theorem intervalAccepted1528 : candidateIntervalCheck candidate1528 (169/200) (8451/10000) piece1528=true := by decide +kernel
noncomputable def cell1528 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1528 accepted1528 (169/200) (8451/10000) piece1528
    intervalAccepted1528 (fun t => piece_le_psi ⟨1286,by decide +kernel⟩ t)
def piece1529 : AffinePiece := pieces[1287]'(by decide +kernel)
theorem intervalAccepted1529 : candidateIntervalCheck candidate1529 (8451/10000) (2113/2500) piece1529=true := by decide +kernel
noncomputable def cell1529 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1529 accepted1529 (8451/10000) (2113/2500) piece1529
    intervalAccepted1529 (fun t => piece_le_psi ⟨1287,by decide +kernel⟩ t)
def piece1530 : AffinePiece := pieces[1288]'(by decide +kernel)
theorem intervalAccepted1530 : candidateIntervalCheck candidate1530 (2113/2500) (8453/10000) piece1530=true := by decide +kernel
noncomputable def cell1530 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1530 accepted1530 (2113/2500) (8453/10000) piece1530
    intervalAccepted1530 (fun t => piece_le_psi ⟨1288,by decide +kernel⟩ t)
def piece1531 : AffinePiece := pieces[1289]'(by decide +kernel)
theorem intervalAccepted1531 : candidateIntervalCheck candidate1531 (8453/10000) (4227/5000) piece1531=true := by decide +kernel
noncomputable def cell1531 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1531 accepted1531 (8453/10000) (4227/5000) piece1531
    intervalAccepted1531 (fun t => piece_le_psi ⟨1289,by decide +kernel⟩ t)
def piece1532 : AffinePiece := pieces[1290]'(by decide +kernel)
theorem intervalAccepted1532 : candidateIntervalCheck candidate1532 (4227/5000) (1691/2000) piece1532=true := by decide +kernel
noncomputable def cell1532 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1532 accepted1532 (4227/5000) (1691/2000) piece1532
    intervalAccepted1532 (fun t => piece_le_psi ⟨1290,by decide +kernel⟩ t)
def piece1533 : AffinePiece := pieces[1291]'(by decide +kernel)
theorem intervalAccepted1533 : candidateIntervalCheck candidate1533 (1691/2000) (1057/1250) piece1533=true := by decide +kernel
noncomputable def cell1533 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1533 accepted1533 (1691/2000) (1057/1250) piece1533
    intervalAccepted1533 (fun t => piece_le_psi ⟨1291,by decide +kernel⟩ t)
def piece1534 : AffinePiece := pieces[1292]'(by decide +kernel)
theorem intervalAccepted1534 : candidateIntervalCheck candidate1534 (1057/1250) (8457/10000) piece1534=true := by decide +kernel
noncomputable def cell1534 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1534 accepted1534 (1057/1250) (8457/10000) piece1534
    intervalAccepted1534 (fun t => piece_le_psi ⟨1292,by decide +kernel⟩ t)
def piece1535 : AffinePiece := pieces[1293]'(by decide +kernel)
theorem intervalAccepted1535 : candidateIntervalCheck candidate1535 (8457/10000) (4229/5000) piece1535=true := by decide +kernel
noncomputable def cell1535 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1535 accepted1535 (8457/10000) (4229/5000) piece1535
    intervalAccepted1535 (fun t => piece_le_psi ⟨1293,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1520, cell1521, cell1522, cell1523, cell1524, cell1525, cell1526, cell1527, cell1528, cell1529, cell1530, cell1531, cell1532, cell1533, cell1534, cell1535]
theorem chainAccepted : spinCellChainCheck (4221/5000) (4229/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4221/5000) (4229/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0095
