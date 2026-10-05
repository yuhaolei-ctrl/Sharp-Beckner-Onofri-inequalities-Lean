import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0102
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0102
open CandidateBatch0102 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1632 : AffinePiece := pieces[1390]'(by decide +kernel)
theorem intervalAccepted1632 : candidateIntervalCheck candidate1632 (4277/5000) (1711/2000) piece1632=true := by decide +kernel
noncomputable def cell1632 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1632 accepted1632 (4277/5000) (1711/2000) piece1632
    intervalAccepted1632 (fun t => piece_le_psi ⟨1390,by decide +kernel⟩ t)
def piece1633 : AffinePiece := pieces[1391]'(by decide +kernel)
theorem intervalAccepted1633 : candidateIntervalCheck candidate1633 (1711/2000) (2139/2500) piece1633=true := by decide +kernel
noncomputable def cell1633 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1633 accepted1633 (1711/2000) (2139/2500) piece1633
    intervalAccepted1633 (fun t => piece_le_psi ⟨1391,by decide +kernel⟩ t)
def piece1634 : AffinePiece := pieces[1392]'(by decide +kernel)
theorem intervalAccepted1634 : candidateIntervalCheck candidate1634 (2139/2500) (8557/10000) piece1634=true := by decide +kernel
noncomputable def cell1634 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1634 accepted1634 (2139/2500) (8557/10000) piece1634
    intervalAccepted1634 (fun t => piece_le_psi ⟨1392,by decide +kernel⟩ t)
def piece1635 : AffinePiece := pieces[1393]'(by decide +kernel)
theorem intervalAccepted1635 : candidateIntervalCheck candidate1635 (8557/10000) (4279/5000) piece1635=true := by decide +kernel
noncomputable def cell1635 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1635 accepted1635 (8557/10000) (4279/5000) piece1635
    intervalAccepted1635 (fun t => piece_le_psi ⟨1393,by decide +kernel⟩ t)
def piece1636 : AffinePiece := pieces[1394]'(by decide +kernel)
theorem intervalAccepted1636 : candidateIntervalCheck candidate1636 (4279/5000) (8559/10000) piece1636=true := by decide +kernel
noncomputable def cell1636 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1636 accepted1636 (4279/5000) (8559/10000) piece1636
    intervalAccepted1636 (fun t => piece_le_psi ⟨1394,by decide +kernel⟩ t)
def piece1637 : AffinePiece := pieces[1395]'(by decide +kernel)
theorem intervalAccepted1637 : candidateIntervalCheck candidate1637 (8559/10000) (107/125) piece1637=true := by decide +kernel
noncomputable def cell1637 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1637 accepted1637 (8559/10000) (107/125) piece1637
    intervalAccepted1637 (fun t => piece_le_psi ⟨1395,by decide +kernel⟩ t)
def piece1638 : AffinePiece := pieces[1396]'(by decide +kernel)
theorem intervalAccepted1638 : candidateIntervalCheck candidate1638 (107/125) (8561/10000) piece1638=true := by decide +kernel
noncomputable def cell1638 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1638 accepted1638 (107/125) (8561/10000) piece1638
    intervalAccepted1638 (fun t => piece_le_psi ⟨1396,by decide +kernel⟩ t)
def piece1639 : AffinePiece := pieces[1397]'(by decide +kernel)
theorem intervalAccepted1639 : candidateIntervalCheck candidate1639 (8561/10000) (4281/5000) piece1639=true := by decide +kernel
noncomputable def cell1639 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1639 accepted1639 (8561/10000) (4281/5000) piece1639
    intervalAccepted1639 (fun t => piece_le_psi ⟨1397,by decide +kernel⟩ t)
def piece1640 : AffinePiece := pieces[1398]'(by decide +kernel)
theorem intervalAccepted1640 : candidateIntervalCheck candidate1640 (4281/5000) (8563/10000) piece1640=true := by decide +kernel
noncomputable def cell1640 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1640 accepted1640 (4281/5000) (8563/10000) piece1640
    intervalAccepted1640 (fun t => piece_le_psi ⟨1398,by decide +kernel⟩ t)
def piece1641 : AffinePiece := pieces[1399]'(by decide +kernel)
theorem intervalAccepted1641 : candidateIntervalCheck candidate1641 (8563/10000) (2141/2500) piece1641=true := by decide +kernel
noncomputable def cell1641 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1641 accepted1641 (8563/10000) (2141/2500) piece1641
    intervalAccepted1641 (fun t => piece_le_psi ⟨1399,by decide +kernel⟩ t)
def piece1642 : AffinePiece := pieces[1400]'(by decide +kernel)
theorem intervalAccepted1642 : candidateIntervalCheck candidate1642 (2141/2500) (1713/2000) piece1642=true := by decide +kernel
noncomputable def cell1642 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1642 accepted1642 (2141/2500) (1713/2000) piece1642
    intervalAccepted1642 (fun t => piece_le_psi ⟨1400,by decide +kernel⟩ t)
def piece1643 : AffinePiece := pieces[1401]'(by decide +kernel)
theorem intervalAccepted1643 : candidateIntervalCheck candidate1643 (1713/2000) (4283/5000) piece1643=true := by decide +kernel
noncomputable def cell1643 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1643 accepted1643 (1713/2000) (4283/5000) piece1643
    intervalAccepted1643 (fun t => piece_le_psi ⟨1401,by decide +kernel⟩ t)
def piece1644 : AffinePiece := pieces[1402]'(by decide +kernel)
theorem intervalAccepted1644 : candidateIntervalCheck candidate1644 (4283/5000) (8567/10000) piece1644=true := by decide +kernel
noncomputable def cell1644 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1644 accepted1644 (4283/5000) (8567/10000) piece1644
    intervalAccepted1644 (fun t => piece_le_psi ⟨1402,by decide +kernel⟩ t)
def piece1645 : AffinePiece := pieces[1403]'(by decide +kernel)
theorem intervalAccepted1645 : candidateIntervalCheck candidate1645 (8567/10000) (1071/1250) piece1645=true := by decide +kernel
noncomputable def cell1645 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1645 accepted1645 (8567/10000) (1071/1250) piece1645
    intervalAccepted1645 (fun t => piece_le_psi ⟨1403,by decide +kernel⟩ t)
def piece1646 : AffinePiece := pieces[1404]'(by decide +kernel)
theorem intervalAccepted1646 : candidateIntervalCheck candidate1646 (1071/1250) (8569/10000) piece1646=true := by decide +kernel
noncomputable def cell1646 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1646 accepted1646 (1071/1250) (8569/10000) piece1646
    intervalAccepted1646 (fun t => piece_le_psi ⟨1404,by decide +kernel⟩ t)
def piece1647 : AffinePiece := pieces[1405]'(by decide +kernel)
theorem intervalAccepted1647 : candidateIntervalCheck candidate1647 (8569/10000) (857/1000) piece1647=true := by decide +kernel
noncomputable def cell1647 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1647 accepted1647 (8569/10000) (857/1000) piece1647
    intervalAccepted1647 (fun t => piece_le_psi ⟨1405,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1632, cell1633, cell1634, cell1635, cell1636, cell1637, cell1638, cell1639, cell1640, cell1641, cell1642, cell1643, cell1644, cell1645, cell1646, cell1647]
theorem chainAccepted : spinCellChainCheck (4277/5000) (857/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4277/5000) (857/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0102
