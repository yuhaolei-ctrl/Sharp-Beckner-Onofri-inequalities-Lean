module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0100

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0100
open CandidateBatch0100 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1600 : AffinePiece := pieces[1358]'(by decide +kernel)
theorem intervalAccepted1600 : candidateIntervalCheck candidate1600 (4261/5000) (8523/10000) piece1600=true := by decide +kernel
noncomputable def cell1600 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1600 accepted1600 (4261/5000) (8523/10000) piece1600
    intervalAccepted1600 (fun t => piece_le_psi ⟨1358,by decide +kernel⟩ t)
def piece1601 : AffinePiece := pieces[1359]'(by decide +kernel)
theorem intervalAccepted1601 : candidateIntervalCheck candidate1601 (8523/10000) (2131/2500) piece1601=true := by decide +kernel
noncomputable def cell1601 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1601 accepted1601 (8523/10000) (2131/2500) piece1601
    intervalAccepted1601 (fun t => piece_le_psi ⟨1359,by decide +kernel⟩ t)
def piece1602 : AffinePiece := pieces[1360]'(by decide +kernel)
theorem intervalAccepted1602 : candidateIntervalCheck candidate1602 (2131/2500) (341/400) piece1602=true := by decide +kernel
noncomputable def cell1602 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1602 accepted1602 (2131/2500) (341/400) piece1602
    intervalAccepted1602 (fun t => piece_le_psi ⟨1360,by decide +kernel⟩ t)
def piece1603 : AffinePiece := pieces[1361]'(by decide +kernel)
theorem intervalAccepted1603 : candidateIntervalCheck candidate1603 (341/400) (4263/5000) piece1603=true := by decide +kernel
noncomputable def cell1603 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1603 accepted1603 (341/400) (4263/5000) piece1603
    intervalAccepted1603 (fun t => piece_le_psi ⟨1361,by decide +kernel⟩ t)
def piece1604 : AffinePiece := pieces[1362]'(by decide +kernel)
theorem intervalAccepted1604 : candidateIntervalCheck candidate1604 (4263/5000) (8527/10000) piece1604=true := by decide +kernel
noncomputable def cell1604 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1604 accepted1604 (4263/5000) (8527/10000) piece1604
    intervalAccepted1604 (fun t => piece_le_psi ⟨1362,by decide +kernel⟩ t)
def piece1605 : AffinePiece := pieces[1363]'(by decide +kernel)
theorem intervalAccepted1605 : candidateIntervalCheck candidate1605 (8527/10000) (533/625) piece1605=true := by decide +kernel
noncomputable def cell1605 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1605 accepted1605 (8527/10000) (533/625) piece1605
    intervalAccepted1605 (fun t => piece_le_psi ⟨1363,by decide +kernel⟩ t)
def piece1606 : AffinePiece := pieces[1364]'(by decide +kernel)
theorem intervalAccepted1606 : candidateIntervalCheck candidate1606 (533/625) (8529/10000) piece1606=true := by decide +kernel
noncomputable def cell1606 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1606 accepted1606 (533/625) (8529/10000) piece1606
    intervalAccepted1606 (fun t => piece_le_psi ⟨1364,by decide +kernel⟩ t)
def piece1607 : AffinePiece := pieces[1365]'(by decide +kernel)
theorem intervalAccepted1607 : candidateIntervalCheck candidate1607 (8529/10000) (853/1000) piece1607=true := by decide +kernel
noncomputable def cell1607 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1607 accepted1607 (8529/10000) (853/1000) piece1607
    intervalAccepted1607 (fun t => piece_le_psi ⟨1365,by decide +kernel⟩ t)
def piece1608 : AffinePiece := pieces[1366]'(by decide +kernel)
theorem intervalAccepted1608 : candidateIntervalCheck candidate1608 (853/1000) (8531/10000) piece1608=true := by decide +kernel
noncomputable def cell1608 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1608 accepted1608 (853/1000) (8531/10000) piece1608
    intervalAccepted1608 (fun t => piece_le_psi ⟨1366,by decide +kernel⟩ t)
def piece1609 : AffinePiece := pieces[1367]'(by decide +kernel)
theorem intervalAccepted1609 : candidateIntervalCheck candidate1609 (8531/10000) (2133/2500) piece1609=true := by decide +kernel
noncomputable def cell1609 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1609 accepted1609 (8531/10000) (2133/2500) piece1609
    intervalAccepted1609 (fun t => piece_le_psi ⟨1367,by decide +kernel⟩ t)
def piece1610 : AffinePiece := pieces[1368]'(by decide +kernel)
theorem intervalAccepted1610 : candidateIntervalCheck candidate1610 (2133/2500) (8533/10000) piece1610=true := by decide +kernel
noncomputable def cell1610 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1610 accepted1610 (2133/2500) (8533/10000) piece1610
    intervalAccepted1610 (fun t => piece_le_psi ⟨1368,by decide +kernel⟩ t)
def piece1611 : AffinePiece := pieces[1369]'(by decide +kernel)
theorem intervalAccepted1611 : candidateIntervalCheck candidate1611 (8533/10000) (4267/5000) piece1611=true := by decide +kernel
noncomputable def cell1611 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1611 accepted1611 (8533/10000) (4267/5000) piece1611
    intervalAccepted1611 (fun t => piece_le_psi ⟨1369,by decide +kernel⟩ t)
def piece1612 : AffinePiece := pieces[1370]'(by decide +kernel)
theorem intervalAccepted1612 : candidateIntervalCheck candidate1612 (4267/5000) (1707/2000) piece1612=true := by decide +kernel
noncomputable def cell1612 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1612 accepted1612 (4267/5000) (1707/2000) piece1612
    intervalAccepted1612 (fun t => piece_le_psi ⟨1370,by decide +kernel⟩ t)
def piece1613 : AffinePiece := pieces[1371]'(by decide +kernel)
theorem intervalAccepted1613 : candidateIntervalCheck candidate1613 (1707/2000) (1067/1250) piece1613=true := by decide +kernel
noncomputable def cell1613 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1613 accepted1613 (1707/2000) (1067/1250) piece1613
    intervalAccepted1613 (fun t => piece_le_psi ⟨1371,by decide +kernel⟩ t)
def piece1614 : AffinePiece := pieces[1372]'(by decide +kernel)
theorem intervalAccepted1614 : candidateIntervalCheck candidate1614 (1067/1250) (8537/10000) piece1614=true := by decide +kernel
noncomputable def cell1614 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1614 accepted1614 (1067/1250) (8537/10000) piece1614
    intervalAccepted1614 (fun t => piece_le_psi ⟨1372,by decide +kernel⟩ t)
def piece1615 : AffinePiece := pieces[1373]'(by decide +kernel)
theorem intervalAccepted1615 : candidateIntervalCheck candidate1615 (8537/10000) (4269/5000) piece1615=true := by decide +kernel
noncomputable def cell1615 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1615 accepted1615 (8537/10000) (4269/5000) piece1615
    intervalAccepted1615 (fun t => piece_le_psi ⟨1373,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1600, cell1601, cell1602, cell1603, cell1604, cell1605, cell1606, cell1607, cell1608, cell1609, cell1610, cell1611, cell1612, cell1613, cell1614, cell1615]
theorem chainAccepted : spinCellChainCheck (4261/5000) (4269/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4261/5000) (4269/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0100
