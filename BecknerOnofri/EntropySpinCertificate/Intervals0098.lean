module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0098

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0098
open CandidateBatch0098 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1568 : AffinePiece := pieces[1326]'(by decide +kernel)
theorem intervalAccepted1568 : candidateIntervalCheck candidate1568 (849/1000) (8491/10000) piece1568=true := by decide +kernel
noncomputable def cell1568 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1568 accepted1568 (849/1000) (8491/10000) piece1568
    intervalAccepted1568 (fun t => piece_le_psi ⟨1326,by decide +kernel⟩ t)
def piece1569 : AffinePiece := pieces[1327]'(by decide +kernel)
theorem intervalAccepted1569 : candidateIntervalCheck candidate1569 (8491/10000) (2123/2500) piece1569=true := by decide +kernel
noncomputable def cell1569 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1569 accepted1569 (8491/10000) (2123/2500) piece1569
    intervalAccepted1569 (fun t => piece_le_psi ⟨1327,by decide +kernel⟩ t)
def piece1570 : AffinePiece := pieces[1328]'(by decide +kernel)
theorem intervalAccepted1570 : candidateIntervalCheck candidate1570 (2123/2500) (8493/10000) piece1570=true := by decide +kernel
noncomputable def cell1570 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1570 accepted1570 (2123/2500) (8493/10000) piece1570
    intervalAccepted1570 (fun t => piece_le_psi ⟨1328,by decide +kernel⟩ t)
def piece1571 : AffinePiece := pieces[1329]'(by decide +kernel)
theorem intervalAccepted1571 : candidateIntervalCheck candidate1571 (8493/10000) (4247/5000) piece1571=true := by decide +kernel
noncomputable def cell1571 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1571 accepted1571 (8493/10000) (4247/5000) piece1571
    intervalAccepted1571 (fun t => piece_le_psi ⟨1329,by decide +kernel⟩ t)
def piece1572 : AffinePiece := pieces[1330]'(by decide +kernel)
theorem intervalAccepted1572 : candidateIntervalCheck candidate1572 (4247/5000) (1699/2000) piece1572=true := by decide +kernel
noncomputable def cell1572 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1572 accepted1572 (4247/5000) (1699/2000) piece1572
    intervalAccepted1572 (fun t => piece_le_psi ⟨1330,by decide +kernel⟩ t)
def piece1573 : AffinePiece := pieces[1331]'(by decide +kernel)
theorem intervalAccepted1573 : candidateIntervalCheck candidate1573 (1699/2000) (531/625) piece1573=true := by decide +kernel
noncomputable def cell1573 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1573 accepted1573 (1699/2000) (531/625) piece1573
    intervalAccepted1573 (fun t => piece_le_psi ⟨1331,by decide +kernel⟩ t)
def piece1574 : AffinePiece := pieces[1332]'(by decide +kernel)
theorem intervalAccepted1574 : candidateIntervalCheck candidate1574 (531/625) (8497/10000) piece1574=true := by decide +kernel
noncomputable def cell1574 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1574 accepted1574 (531/625) (8497/10000) piece1574
    intervalAccepted1574 (fun t => piece_le_psi ⟨1332,by decide +kernel⟩ t)
def piece1575 : AffinePiece := pieces[1333]'(by decide +kernel)
theorem intervalAccepted1575 : candidateIntervalCheck candidate1575 (8497/10000) (4249/5000) piece1575=true := by decide +kernel
noncomputable def cell1575 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1575 accepted1575 (8497/10000) (4249/5000) piece1575
    intervalAccepted1575 (fun t => piece_le_psi ⟨1333,by decide +kernel⟩ t)
def piece1576 : AffinePiece := pieces[1334]'(by decide +kernel)
theorem intervalAccepted1576 : candidateIntervalCheck candidate1576 (4249/5000) (8499/10000) piece1576=true := by decide +kernel
noncomputable def cell1576 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1576 accepted1576 (4249/5000) (8499/10000) piece1576
    intervalAccepted1576 (fun t => piece_le_psi ⟨1334,by decide +kernel⟩ t)
def piece1577 : AffinePiece := pieces[1335]'(by decide +kernel)
theorem intervalAccepted1577 : candidateIntervalCheck candidate1577 (8499/10000) (17/20) piece1577=true := by decide +kernel
noncomputable def cell1577 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1577 accepted1577 (8499/10000) (17/20) piece1577
    intervalAccepted1577 (fun t => piece_le_psi ⟨1335,by decide +kernel⟩ t)
def piece1578 : AffinePiece := pieces[1336]'(by decide +kernel)
theorem intervalAccepted1578 : candidateIntervalCheck candidate1578 (17/20) (8501/10000) piece1578=true := by decide +kernel
noncomputable def cell1578 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1578 accepted1578 (17/20) (8501/10000) piece1578
    intervalAccepted1578 (fun t => piece_le_psi ⟨1336,by decide +kernel⟩ t)
def piece1579 : AffinePiece := pieces[1337]'(by decide +kernel)
theorem intervalAccepted1579 : candidateIntervalCheck candidate1579 (8501/10000) (4251/5000) piece1579=true := by decide +kernel
noncomputable def cell1579 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1579 accepted1579 (8501/10000) (4251/5000) piece1579
    intervalAccepted1579 (fun t => piece_le_psi ⟨1337,by decide +kernel⟩ t)
def piece1580 : AffinePiece := pieces[1338]'(by decide +kernel)
theorem intervalAccepted1580 : candidateIntervalCheck candidate1580 (4251/5000) (8503/10000) piece1580=true := by decide +kernel
noncomputable def cell1580 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1580 accepted1580 (4251/5000) (8503/10000) piece1580
    intervalAccepted1580 (fun t => piece_le_psi ⟨1338,by decide +kernel⟩ t)
def piece1581 : AffinePiece := pieces[1339]'(by decide +kernel)
theorem intervalAccepted1581 : candidateIntervalCheck candidate1581 (8503/10000) (1063/1250) piece1581=true := by decide +kernel
noncomputable def cell1581 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1581 accepted1581 (8503/10000) (1063/1250) piece1581
    intervalAccepted1581 (fun t => piece_le_psi ⟨1339,by decide +kernel⟩ t)
def piece1582 : AffinePiece := pieces[1340]'(by decide +kernel)
theorem intervalAccepted1582 : candidateIntervalCheck candidate1582 (1063/1250) (1701/2000) piece1582=true := by decide +kernel
noncomputable def cell1582 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1582 accepted1582 (1063/1250) (1701/2000) piece1582
    intervalAccepted1582 (fun t => piece_le_psi ⟨1340,by decide +kernel⟩ t)
def piece1583 : AffinePiece := pieces[1341]'(by decide +kernel)
theorem intervalAccepted1583 : candidateIntervalCheck candidate1583 (1701/2000) (4253/5000) piece1583=true := by decide +kernel
noncomputable def cell1583 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1583 accepted1583 (1701/2000) (4253/5000) piece1583
    intervalAccepted1583 (fun t => piece_le_psi ⟨1341,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1568, cell1569, cell1570, cell1571, cell1572, cell1573, cell1574, cell1575, cell1576, cell1577, cell1578, cell1579, cell1580, cell1581, cell1582, cell1583]
theorem chainAccepted : spinCellChainCheck (849/1000) (4253/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (849/1000) (4253/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0098
