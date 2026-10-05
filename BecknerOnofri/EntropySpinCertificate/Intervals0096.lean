module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0096

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0096
open CandidateBatch0096 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1536 : AffinePiece := pieces[1294]'(by decide +kernel)
theorem intervalAccepted1536 : candidateIntervalCheck candidate1536 (4229/5000) (8459/10000) piece1536=true := by decide +kernel
noncomputable def cell1536 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1536 accepted1536 (4229/5000) (8459/10000) piece1536
    intervalAccepted1536 (fun t => piece_le_psi ⟨1294,by decide +kernel⟩ t)
def piece1537 : AffinePiece := pieces[1295]'(by decide +kernel)
theorem intervalAccepted1537 : candidateIntervalCheck candidate1537 (8459/10000) (423/500) piece1537=true := by decide +kernel
noncomputable def cell1537 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1537 accepted1537 (8459/10000) (423/500) piece1537
    intervalAccepted1537 (fun t => piece_le_psi ⟨1295,by decide +kernel⟩ t)
def piece1538 : AffinePiece := pieces[1296]'(by decide +kernel)
theorem intervalAccepted1538 : candidateIntervalCheck candidate1538 (423/500) (8461/10000) piece1538=true := by decide +kernel
noncomputable def cell1538 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1538 accepted1538 (423/500) (8461/10000) piece1538
    intervalAccepted1538 (fun t => piece_le_psi ⟨1296,by decide +kernel⟩ t)
def piece1539 : AffinePiece := pieces[1297]'(by decide +kernel)
theorem intervalAccepted1539 : candidateIntervalCheck candidate1539 (8461/10000) (4231/5000) piece1539=true := by decide +kernel
noncomputable def cell1539 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1539 accepted1539 (8461/10000) (4231/5000) piece1539
    intervalAccepted1539 (fun t => piece_le_psi ⟨1297,by decide +kernel⟩ t)
def piece1540 : AffinePiece := pieces[1298]'(by decide +kernel)
theorem intervalAccepted1540 : candidateIntervalCheck candidate1540 (4231/5000) (8463/10000) piece1540=true := by decide +kernel
noncomputable def cell1540 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1540 accepted1540 (4231/5000) (8463/10000) piece1540
    intervalAccepted1540 (fun t => piece_le_psi ⟨1298,by decide +kernel⟩ t)
def piece1541 : AffinePiece := pieces[1299]'(by decide +kernel)
theorem intervalAccepted1541 : candidateIntervalCheck candidate1541 (8463/10000) (529/625) piece1541=true := by decide +kernel
noncomputable def cell1541 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1541 accepted1541 (8463/10000) (529/625) piece1541
    intervalAccepted1541 (fun t => piece_le_psi ⟨1299,by decide +kernel⟩ t)
def piece1542 : AffinePiece := pieces[1300]'(by decide +kernel)
theorem intervalAccepted1542 : candidateIntervalCheck candidate1542 (529/625) (1693/2000) piece1542=true := by decide +kernel
noncomputable def cell1542 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1542 accepted1542 (529/625) (1693/2000) piece1542
    intervalAccepted1542 (fun t => piece_le_psi ⟨1300,by decide +kernel⟩ t)
def piece1543 : AffinePiece := pieces[1301]'(by decide +kernel)
theorem intervalAccepted1543 : candidateIntervalCheck candidate1543 (1693/2000) (4233/5000) piece1543=true := by decide +kernel
noncomputable def cell1543 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1543 accepted1543 (1693/2000) (4233/5000) piece1543
    intervalAccepted1543 (fun t => piece_le_psi ⟨1301,by decide +kernel⟩ t)
def piece1544 : AffinePiece := pieces[1302]'(by decide +kernel)
theorem intervalAccepted1544 : candidateIntervalCheck candidate1544 (4233/5000) (8467/10000) piece1544=true := by decide +kernel
noncomputable def cell1544 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1544 accepted1544 (4233/5000) (8467/10000) piece1544
    intervalAccepted1544 (fun t => piece_le_psi ⟨1302,by decide +kernel⟩ t)
def piece1545 : AffinePiece := pieces[1303]'(by decide +kernel)
theorem intervalAccepted1545 : candidateIntervalCheck candidate1545 (8467/10000) (2117/2500) piece1545=true := by decide +kernel
noncomputable def cell1545 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1545 accepted1545 (8467/10000) (2117/2500) piece1545
    intervalAccepted1545 (fun t => piece_le_psi ⟨1303,by decide +kernel⟩ t)
def piece1546 : AffinePiece := pieces[1304]'(by decide +kernel)
theorem intervalAccepted1546 : candidateIntervalCheck candidate1546 (2117/2500) (8469/10000) piece1546=true := by decide +kernel
noncomputable def cell1546 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1546 accepted1546 (2117/2500) (8469/10000) piece1546
    intervalAccepted1546 (fun t => piece_le_psi ⟨1304,by decide +kernel⟩ t)
def piece1547 : AffinePiece := pieces[1305]'(by decide +kernel)
theorem intervalAccepted1547 : candidateIntervalCheck candidate1547 (8469/10000) (847/1000) piece1547=true := by decide +kernel
noncomputable def cell1547 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1547 accepted1547 (8469/10000) (847/1000) piece1547
    intervalAccepted1547 (fun t => piece_le_psi ⟨1305,by decide +kernel⟩ t)
def piece1548 : AffinePiece := pieces[1306]'(by decide +kernel)
theorem intervalAccepted1548 : candidateIntervalCheck candidate1548 (847/1000) (8471/10000) piece1548=true := by decide +kernel
noncomputable def cell1548 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1548 accepted1548 (847/1000) (8471/10000) piece1548
    intervalAccepted1548 (fun t => piece_le_psi ⟨1306,by decide +kernel⟩ t)
def piece1549 : AffinePiece := pieces[1307]'(by decide +kernel)
theorem intervalAccepted1549 : candidateIntervalCheck candidate1549 (8471/10000) (1059/1250) piece1549=true := by decide +kernel
noncomputable def cell1549 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1549 accepted1549 (8471/10000) (1059/1250) piece1549
    intervalAccepted1549 (fun t => piece_le_psi ⟨1307,by decide +kernel⟩ t)
def piece1550 : AffinePiece := pieces[1308]'(by decide +kernel)
theorem intervalAccepted1550 : candidateIntervalCheck candidate1550 (1059/1250) (8473/10000) piece1550=true := by decide +kernel
noncomputable def cell1550 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1550 accepted1550 (1059/1250) (8473/10000) piece1550
    intervalAccepted1550 (fun t => piece_le_psi ⟨1308,by decide +kernel⟩ t)
def piece1551 : AffinePiece := pieces[1309]'(by decide +kernel)
theorem intervalAccepted1551 : candidateIntervalCheck candidate1551 (8473/10000) (4237/5000) piece1551=true := by decide +kernel
noncomputable def cell1551 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1551 accepted1551 (8473/10000) (4237/5000) piece1551
    intervalAccepted1551 (fun t => piece_le_psi ⟨1309,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1536, cell1537, cell1538, cell1539, cell1540, cell1541, cell1542, cell1543, cell1544, cell1545, cell1546, cell1547, cell1548, cell1549, cell1550, cell1551]
theorem chainAccepted : spinCellChainCheck (4229/5000) (4237/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4229/5000) (4237/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0096
