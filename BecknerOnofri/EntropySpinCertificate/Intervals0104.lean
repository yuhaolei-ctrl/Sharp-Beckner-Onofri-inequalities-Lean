module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0104

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0104
open CandidateBatch0104 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1664 : AffinePiece := pieces[1422]'(by decide +kernel)
theorem intervalAccepted1664 : candidateIntervalCheck candidate1664 (4293/5000) (8587/10000) piece1664=true := by decide +kernel
noncomputable def cell1664 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1664 accepted1664 (4293/5000) (8587/10000) piece1664
    intervalAccepted1664 (fun t => piece_le_psi ⟨1422,by decide +kernel⟩ t)
def piece1665 : AffinePiece := pieces[1423]'(by decide +kernel)
theorem intervalAccepted1665 : candidateIntervalCheck candidate1665 (8587/10000) (2147/2500) piece1665=true := by decide +kernel
noncomputable def cell1665 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1665 accepted1665 (8587/10000) (2147/2500) piece1665
    intervalAccepted1665 (fun t => piece_le_psi ⟨1423,by decide +kernel⟩ t)
def piece1666 : AffinePiece := pieces[1424]'(by decide +kernel)
theorem intervalAccepted1666 : candidateIntervalCheck candidate1666 (2147/2500) (8589/10000) piece1666=true := by decide +kernel
noncomputable def cell1666 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1666 accepted1666 (2147/2500) (8589/10000) piece1666
    intervalAccepted1666 (fun t => piece_le_psi ⟨1424,by decide +kernel⟩ t)
def piece1667 : AffinePiece := pieces[1425]'(by decide +kernel)
theorem intervalAccepted1667 : candidateIntervalCheck candidate1667 (8589/10000) (859/1000) piece1667=true := by decide +kernel
noncomputable def cell1667 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1667 accepted1667 (8589/10000) (859/1000) piece1667
    intervalAccepted1667 (fun t => piece_le_psi ⟨1425,by decide +kernel⟩ t)
def piece1668 : AffinePiece := pieces[1426]'(by decide +kernel)
theorem intervalAccepted1668 : candidateIntervalCheck candidate1668 (859/1000) (8591/10000) piece1668=true := by decide +kernel
noncomputable def cell1668 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1668 accepted1668 (859/1000) (8591/10000) piece1668
    intervalAccepted1668 (fun t => piece_le_psi ⟨1426,by decide +kernel⟩ t)
def piece1669 : AffinePiece := pieces[1427]'(by decide +kernel)
theorem intervalAccepted1669 : candidateIntervalCheck candidate1669 (8591/10000) (537/625) piece1669=true := by decide +kernel
noncomputable def cell1669 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1669 accepted1669 (8591/10000) (537/625) piece1669
    intervalAccepted1669 (fun t => piece_le_psi ⟨1427,by decide +kernel⟩ t)
def piece1670 : AffinePiece := pieces[1428]'(by decide +kernel)
theorem intervalAccepted1670 : candidateIntervalCheck candidate1670 (537/625) (8593/10000) piece1670=true := by decide +kernel
noncomputable def cell1670 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1670 accepted1670 (537/625) (8593/10000) piece1670
    intervalAccepted1670 (fun t => piece_le_psi ⟨1428,by decide +kernel⟩ t)
def piece1671 : AffinePiece := pieces[1429]'(by decide +kernel)
theorem intervalAccepted1671 : candidateIntervalCheck candidate1671 (8593/10000) (4297/5000) piece1671=true := by decide +kernel
noncomputable def cell1671 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1671 accepted1671 (8593/10000) (4297/5000) piece1671
    intervalAccepted1671 (fun t => piece_le_psi ⟨1429,by decide +kernel⟩ t)
def piece1672 : AffinePiece := pieces[1430]'(by decide +kernel)
theorem intervalAccepted1672 : candidateIntervalCheck candidate1672 (4297/5000) (1719/2000) piece1672=true := by decide +kernel
noncomputable def cell1672 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1672 accepted1672 (4297/5000) (1719/2000) piece1672
    intervalAccepted1672 (fun t => piece_le_psi ⟨1430,by decide +kernel⟩ t)
def piece1673 : AffinePiece := pieces[1431]'(by decide +kernel)
theorem intervalAccepted1673 : candidateIntervalCheck candidate1673 (1719/2000) (2149/2500) piece1673=true := by decide +kernel
noncomputable def cell1673 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1673 accepted1673 (1719/2000) (2149/2500) piece1673
    intervalAccepted1673 (fun t => piece_le_psi ⟨1431,by decide +kernel⟩ t)
def piece1674 : AffinePiece := pieces[1432]'(by decide +kernel)
theorem intervalAccepted1674 : candidateIntervalCheck candidate1674 (2149/2500) (8597/10000) piece1674=true := by decide +kernel
noncomputable def cell1674 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1674 accepted1674 (2149/2500) (8597/10000) piece1674
    intervalAccepted1674 (fun t => piece_le_psi ⟨1432,by decide +kernel⟩ t)
def piece1675 : AffinePiece := pieces[1433]'(by decide +kernel)
theorem intervalAccepted1675 : candidateIntervalCheck candidate1675 (8597/10000) (4299/5000) piece1675=true := by decide +kernel
noncomputable def cell1675 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1675 accepted1675 (8597/10000) (4299/5000) piece1675
    intervalAccepted1675 (fun t => piece_le_psi ⟨1433,by decide +kernel⟩ t)
def piece1676 : AffinePiece := pieces[1434]'(by decide +kernel)
theorem intervalAccepted1676 : candidateIntervalCheck candidate1676 (4299/5000) (8599/10000) piece1676=true := by decide +kernel
noncomputable def cell1676 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1676 accepted1676 (4299/5000) (8599/10000) piece1676
    intervalAccepted1676 (fun t => piece_le_psi ⟨1434,by decide +kernel⟩ t)
def piece1677 : AffinePiece := pieces[1435]'(by decide +kernel)
theorem intervalAccepted1677 : candidateIntervalCheck candidate1677 (8599/10000) (43/50) piece1677=true := by decide +kernel
noncomputable def cell1677 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1677 accepted1677 (8599/10000) (43/50) piece1677
    intervalAccepted1677 (fun t => piece_le_psi ⟨1435,by decide +kernel⟩ t)
def piece1678 : AffinePiece := pieces[1436]'(by decide +kernel)
theorem intervalAccepted1678 : candidateIntervalCheck candidate1678 (43/50) (8601/10000) piece1678=true := by decide +kernel
noncomputable def cell1678 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1678 accepted1678 (43/50) (8601/10000) piece1678
    intervalAccepted1678 (fun t => piece_le_psi ⟨1436,by decide +kernel⟩ t)
def piece1679 : AffinePiece := pieces[1437]'(by decide +kernel)
theorem intervalAccepted1679 : candidateIntervalCheck candidate1679 (8601/10000) (4301/5000) piece1679=true := by decide +kernel
noncomputable def cell1679 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1679 accepted1679 (8601/10000) (4301/5000) piece1679
    intervalAccepted1679 (fun t => piece_le_psi ⟨1437,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1664, cell1665, cell1666, cell1667, cell1668, cell1669, cell1670, cell1671, cell1672, cell1673, cell1674, cell1675, cell1676, cell1677, cell1678, cell1679]
theorem chainAccepted : spinCellChainCheck (4293/5000) (4301/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4293/5000) (4301/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0104
