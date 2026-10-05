import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0099
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0099
open CandidateBatch0099 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1584 : AffinePiece := pieces[1342]'(by decide +kernel)
theorem intervalAccepted1584 : candidateIntervalCheck candidate1584 (4253/5000) (8507/10000) piece1584=true := by decide +kernel
noncomputable def cell1584 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1584 accepted1584 (4253/5000) (8507/10000) piece1584
    intervalAccepted1584 (fun t => piece_le_psi ⟨1342,by decide +kernel⟩ t)
def piece1585 : AffinePiece := pieces[1343]'(by decide +kernel)
theorem intervalAccepted1585 : candidateIntervalCheck candidate1585 (8507/10000) (2127/2500) piece1585=true := by decide +kernel
noncomputable def cell1585 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1585 accepted1585 (8507/10000) (2127/2500) piece1585
    intervalAccepted1585 (fun t => piece_le_psi ⟨1343,by decide +kernel⟩ t)
def piece1586 : AffinePiece := pieces[1344]'(by decide +kernel)
theorem intervalAccepted1586 : candidateIntervalCheck candidate1586 (2127/2500) (8509/10000) piece1586=true := by decide +kernel
noncomputable def cell1586 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1586 accepted1586 (2127/2500) (8509/10000) piece1586
    intervalAccepted1586 (fun t => piece_le_psi ⟨1344,by decide +kernel⟩ t)
def piece1587 : AffinePiece := pieces[1345]'(by decide +kernel)
theorem intervalAccepted1587 : candidateIntervalCheck candidate1587 (8509/10000) (851/1000) piece1587=true := by decide +kernel
noncomputable def cell1587 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1587 accepted1587 (8509/10000) (851/1000) piece1587
    intervalAccepted1587 (fun t => piece_le_psi ⟨1345,by decide +kernel⟩ t)
def piece1588 : AffinePiece := pieces[1346]'(by decide +kernel)
theorem intervalAccepted1588 : candidateIntervalCheck candidate1588 (851/1000) (8511/10000) piece1588=true := by decide +kernel
noncomputable def cell1588 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1588 accepted1588 (851/1000) (8511/10000) piece1588
    intervalAccepted1588 (fun t => piece_le_psi ⟨1346,by decide +kernel⟩ t)
def piece1589 : AffinePiece := pieces[1347]'(by decide +kernel)
theorem intervalAccepted1589 : candidateIntervalCheck candidate1589 (8511/10000) (532/625) piece1589=true := by decide +kernel
noncomputable def cell1589 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1589 accepted1589 (8511/10000) (532/625) piece1589
    intervalAccepted1589 (fun t => piece_le_psi ⟨1347,by decide +kernel⟩ t)
def piece1590 : AffinePiece := pieces[1348]'(by decide +kernel)
theorem intervalAccepted1590 : candidateIntervalCheck candidate1590 (532/625) (8513/10000) piece1590=true := by decide +kernel
noncomputable def cell1590 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1590 accepted1590 (532/625) (8513/10000) piece1590
    intervalAccepted1590 (fun t => piece_le_psi ⟨1348,by decide +kernel⟩ t)
def piece1591 : AffinePiece := pieces[1349]'(by decide +kernel)
theorem intervalAccepted1591 : candidateIntervalCheck candidate1591 (8513/10000) (4257/5000) piece1591=true := by decide +kernel
noncomputable def cell1591 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1591 accepted1591 (8513/10000) (4257/5000) piece1591
    intervalAccepted1591 (fun t => piece_le_psi ⟨1349,by decide +kernel⟩ t)
def piece1592 : AffinePiece := pieces[1350]'(by decide +kernel)
theorem intervalAccepted1592 : candidateIntervalCheck candidate1592 (4257/5000) (1703/2000) piece1592=true := by decide +kernel
noncomputable def cell1592 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1592 accepted1592 (4257/5000) (1703/2000) piece1592
    intervalAccepted1592 (fun t => piece_le_psi ⟨1350,by decide +kernel⟩ t)
def piece1593 : AffinePiece := pieces[1351]'(by decide +kernel)
theorem intervalAccepted1593 : candidateIntervalCheck candidate1593 (1703/2000) (2129/2500) piece1593=true := by decide +kernel
noncomputable def cell1593 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1593 accepted1593 (1703/2000) (2129/2500) piece1593
    intervalAccepted1593 (fun t => piece_le_psi ⟨1351,by decide +kernel⟩ t)
def piece1594 : AffinePiece := pieces[1352]'(by decide +kernel)
theorem intervalAccepted1594 : candidateIntervalCheck candidate1594 (2129/2500) (8517/10000) piece1594=true := by decide +kernel
noncomputable def cell1594 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1594 accepted1594 (2129/2500) (8517/10000) piece1594
    intervalAccepted1594 (fun t => piece_le_psi ⟨1352,by decide +kernel⟩ t)
def piece1595 : AffinePiece := pieces[1353]'(by decide +kernel)
theorem intervalAccepted1595 : candidateIntervalCheck candidate1595 (8517/10000) (4259/5000) piece1595=true := by decide +kernel
noncomputable def cell1595 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1595 accepted1595 (8517/10000) (4259/5000) piece1595
    intervalAccepted1595 (fun t => piece_le_psi ⟨1353,by decide +kernel⟩ t)
def piece1596 : AffinePiece := pieces[1354]'(by decide +kernel)
theorem intervalAccepted1596 : candidateIntervalCheck candidate1596 (4259/5000) (8519/10000) piece1596=true := by decide +kernel
noncomputable def cell1596 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1596 accepted1596 (4259/5000) (8519/10000) piece1596
    intervalAccepted1596 (fun t => piece_le_psi ⟨1354,by decide +kernel⟩ t)
def piece1597 : AffinePiece := pieces[1355]'(by decide +kernel)
theorem intervalAccepted1597 : candidateIntervalCheck candidate1597 (8519/10000) (213/250) piece1597=true := by decide +kernel
noncomputable def cell1597 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1597 accepted1597 (8519/10000) (213/250) piece1597
    intervalAccepted1597 (fun t => piece_le_psi ⟨1355,by decide +kernel⟩ t)
def piece1598 : AffinePiece := pieces[1356]'(by decide +kernel)
theorem intervalAccepted1598 : candidateIntervalCheck candidate1598 (213/250) (8521/10000) piece1598=true := by decide +kernel
noncomputable def cell1598 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1598 accepted1598 (213/250) (8521/10000) piece1598
    intervalAccepted1598 (fun t => piece_le_psi ⟨1356,by decide +kernel⟩ t)
def piece1599 : AffinePiece := pieces[1357]'(by decide +kernel)
theorem intervalAccepted1599 : candidateIntervalCheck candidate1599 (8521/10000) (4261/5000) piece1599=true := by decide +kernel
noncomputable def cell1599 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1599 accepted1599 (8521/10000) (4261/5000) piece1599
    intervalAccepted1599 (fun t => piece_le_psi ⟨1357,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1584, cell1585, cell1586, cell1587, cell1588, cell1589, cell1590, cell1591, cell1592, cell1593, cell1594, cell1595, cell1596, cell1597, cell1598, cell1599]
theorem chainAccepted : spinCellChainCheck (4253/5000) (4261/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4253/5000) (4261/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0099
