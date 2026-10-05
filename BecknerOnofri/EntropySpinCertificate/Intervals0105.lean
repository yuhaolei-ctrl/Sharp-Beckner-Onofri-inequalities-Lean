import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0105
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0105
open CandidateBatch0105 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1680 : AffinePiece := pieces[1438]'(by decide +kernel)
theorem intervalAccepted1680 : candidateIntervalCheck candidate1680 (4301/5000) (8603/10000) piece1680=true := by decide +kernel
noncomputable def cell1680 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1680 accepted1680 (4301/5000) (8603/10000) piece1680
    intervalAccepted1680 (fun t => piece_le_psi ⟨1438,by decide +kernel⟩ t)
def piece1681 : AffinePiece := pieces[1439]'(by decide +kernel)
theorem intervalAccepted1681 : candidateIntervalCheck candidate1681 (8603/10000) (2151/2500) piece1681=true := by decide +kernel
noncomputable def cell1681 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1681 accepted1681 (8603/10000) (2151/2500) piece1681
    intervalAccepted1681 (fun t => piece_le_psi ⟨1439,by decide +kernel⟩ t)
def piece1682 : AffinePiece := pieces[1440]'(by decide +kernel)
theorem intervalAccepted1682 : candidateIntervalCheck candidate1682 (2151/2500) (1721/2000) piece1682=true := by decide +kernel
noncomputable def cell1682 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1682 accepted1682 (2151/2500) (1721/2000) piece1682
    intervalAccepted1682 (fun t => piece_le_psi ⟨1440,by decide +kernel⟩ t)
def piece1683 : AffinePiece := pieces[1441]'(by decide +kernel)
theorem intervalAccepted1683 : candidateIntervalCheck candidate1683 (1721/2000) (4303/5000) piece1683=true := by decide +kernel
noncomputable def cell1683 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1683 accepted1683 (1721/2000) (4303/5000) piece1683
    intervalAccepted1683 (fun t => piece_le_psi ⟨1441,by decide +kernel⟩ t)
def piece1684 : AffinePiece := pieces[1442]'(by decide +kernel)
theorem intervalAccepted1684 : candidateIntervalCheck candidate1684 (4303/5000) (8607/10000) piece1684=true := by decide +kernel
noncomputable def cell1684 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1684 accepted1684 (4303/5000) (8607/10000) piece1684
    intervalAccepted1684 (fun t => piece_le_psi ⟨1442,by decide +kernel⟩ t)
def piece1685 : AffinePiece := pieces[1443]'(by decide +kernel)
theorem intervalAccepted1685 : candidateIntervalCheck candidate1685 (8607/10000) (538/625) piece1685=true := by decide +kernel
noncomputable def cell1685 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1685 accepted1685 (8607/10000) (538/625) piece1685
    intervalAccepted1685 (fun t => piece_le_psi ⟨1443,by decide +kernel⟩ t)
def piece1686 : AffinePiece := pieces[1444]'(by decide +kernel)
theorem intervalAccepted1686 : candidateIntervalCheck candidate1686 (538/625) (8609/10000) piece1686=true := by decide +kernel
noncomputable def cell1686 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1686 accepted1686 (538/625) (8609/10000) piece1686
    intervalAccepted1686 (fun t => piece_le_psi ⟨1444,by decide +kernel⟩ t)
def piece1687 : AffinePiece := pieces[1445]'(by decide +kernel)
theorem intervalAccepted1687 : candidateIntervalCheck candidate1687 (8609/10000) (861/1000) piece1687=true := by decide +kernel
noncomputable def cell1687 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1687 accepted1687 (8609/10000) (861/1000) piece1687
    intervalAccepted1687 (fun t => piece_le_psi ⟨1445,by decide +kernel⟩ t)
def piece1688 : AffinePiece := pieces[1446]'(by decide +kernel)
theorem intervalAccepted1688 : candidateIntervalCheck candidate1688 (861/1000) (8611/10000) piece1688=true := by decide +kernel
noncomputable def cell1688 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1688 accepted1688 (861/1000) (8611/10000) piece1688
    intervalAccepted1688 (fun t => piece_le_psi ⟨1446,by decide +kernel⟩ t)
def piece1689 : AffinePiece := pieces[1447]'(by decide +kernel)
theorem intervalAccepted1689 : candidateIntervalCheck candidate1689 (8611/10000) (2153/2500) piece1689=true := by decide +kernel
noncomputable def cell1689 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1689 accepted1689 (8611/10000) (2153/2500) piece1689
    intervalAccepted1689 (fun t => piece_le_psi ⟨1447,by decide +kernel⟩ t)
def piece1690 : AffinePiece := pieces[1448]'(by decide +kernel)
theorem intervalAccepted1690 : candidateIntervalCheck candidate1690 (2153/2500) (8613/10000) piece1690=true := by decide +kernel
noncomputable def cell1690 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1690 accepted1690 (2153/2500) (8613/10000) piece1690
    intervalAccepted1690 (fun t => piece_le_psi ⟨1448,by decide +kernel⟩ t)
def piece1691 : AffinePiece := pieces[1449]'(by decide +kernel)
theorem intervalAccepted1691 : candidateIntervalCheck candidate1691 (8613/10000) (4307/5000) piece1691=true := by decide +kernel
noncomputable def cell1691 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1691 accepted1691 (8613/10000) (4307/5000) piece1691
    intervalAccepted1691 (fun t => piece_le_psi ⟨1449,by decide +kernel⟩ t)
def piece1692 : AffinePiece := pieces[1450]'(by decide +kernel)
theorem intervalAccepted1692 : candidateIntervalCheck candidate1692 (4307/5000) (1723/2000) piece1692=true := by decide +kernel
noncomputable def cell1692 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1692 accepted1692 (4307/5000) (1723/2000) piece1692
    intervalAccepted1692 (fun t => piece_le_psi ⟨1450,by decide +kernel⟩ t)
def piece1693 : AffinePiece := pieces[1451]'(by decide +kernel)
theorem intervalAccepted1693 : candidateIntervalCheck candidate1693 (1723/2000) (1077/1250) piece1693=true := by decide +kernel
noncomputable def cell1693 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1693 accepted1693 (1723/2000) (1077/1250) piece1693
    intervalAccepted1693 (fun t => piece_le_psi ⟨1451,by decide +kernel⟩ t)
def piece1694 : AffinePiece := pieces[1452]'(by decide +kernel)
theorem intervalAccepted1694 : candidateIntervalCheck candidate1694 (1077/1250) (8617/10000) piece1694=true := by decide +kernel
noncomputable def cell1694 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1694 accepted1694 (1077/1250) (8617/10000) piece1694
    intervalAccepted1694 (fun t => piece_le_psi ⟨1452,by decide +kernel⟩ t)
def piece1695 : AffinePiece := pieces[1453]'(by decide +kernel)
theorem intervalAccepted1695 : candidateIntervalCheck candidate1695 (8617/10000) (4309/5000) piece1695=true := by decide +kernel
noncomputable def cell1695 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1695 accepted1695 (8617/10000) (4309/5000) piece1695
    intervalAccepted1695 (fun t => piece_le_psi ⟨1453,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1680, cell1681, cell1682, cell1683, cell1684, cell1685, cell1686, cell1687, cell1688, cell1689, cell1690, cell1691, cell1692, cell1693, cell1694, cell1695]
theorem chainAccepted : spinCellChainCheck (4301/5000) (4309/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4301/5000) (4309/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0105
