module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0106

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0106
open CandidateBatch0106 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1696 : AffinePiece := pieces[1454]'(by decide +kernel)
theorem intervalAccepted1696 : candidateIntervalCheck candidate1696 (4309/5000) (8619/10000) piece1696=true := by decide +kernel
noncomputable def cell1696 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1696 accepted1696 (4309/5000) (8619/10000) piece1696
    intervalAccepted1696 (fun t => piece_le_psi ⟨1454,by decide +kernel⟩ t)
def piece1697 : AffinePiece := pieces[1455]'(by decide +kernel)
theorem intervalAccepted1697 : candidateIntervalCheck candidate1697 (8619/10000) (431/500) piece1697=true := by decide +kernel
noncomputable def cell1697 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1697 accepted1697 (8619/10000) (431/500) piece1697
    intervalAccepted1697 (fun t => piece_le_psi ⟨1455,by decide +kernel⟩ t)
def piece1698 : AffinePiece := pieces[1456]'(by decide +kernel)
theorem intervalAccepted1698 : candidateIntervalCheck candidate1698 (431/500) (8621/10000) piece1698=true := by decide +kernel
noncomputable def cell1698 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1698 accepted1698 (431/500) (8621/10000) piece1698
    intervalAccepted1698 (fun t => piece_le_psi ⟨1456,by decide +kernel⟩ t)
def piece1699 : AffinePiece := pieces[1457]'(by decide +kernel)
theorem intervalAccepted1699 : candidateIntervalCheck candidate1699 (8621/10000) (4311/5000) piece1699=true := by decide +kernel
noncomputable def cell1699 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1699 accepted1699 (8621/10000) (4311/5000) piece1699
    intervalAccepted1699 (fun t => piece_le_psi ⟨1457,by decide +kernel⟩ t)
def piece1700 : AffinePiece := pieces[1458]'(by decide +kernel)
theorem intervalAccepted1700 : candidateIntervalCheck candidate1700 (4311/5000) (8623/10000) piece1700=true := by decide +kernel
noncomputable def cell1700 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1700 accepted1700 (4311/5000) (8623/10000) piece1700
    intervalAccepted1700 (fun t => piece_le_psi ⟨1458,by decide +kernel⟩ t)
def piece1701 : AffinePiece := pieces[1459]'(by decide +kernel)
theorem intervalAccepted1701 : candidateIntervalCheck candidate1701 (8623/10000) (539/625) piece1701=true := by decide +kernel
noncomputable def cell1701 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1701 accepted1701 (8623/10000) (539/625) piece1701
    intervalAccepted1701 (fun t => piece_le_psi ⟨1459,by decide +kernel⟩ t)
def piece1702 : AffinePiece := pieces[1460]'(by decide +kernel)
theorem intervalAccepted1702 : candidateIntervalCheck candidate1702 (539/625) (69/80) piece1702=true := by decide +kernel
noncomputable def cell1702 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1702 accepted1702 (539/625) (69/80) piece1702
    intervalAccepted1702 (fun t => piece_le_psi ⟨1460,by decide +kernel⟩ t)
def piece1703 : AffinePiece := pieces[1461]'(by decide +kernel)
theorem intervalAccepted1703 : candidateIntervalCheck candidate1703 (69/80) (4313/5000) piece1703=true := by decide +kernel
noncomputable def cell1703 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1703 accepted1703 (69/80) (4313/5000) piece1703
    intervalAccepted1703 (fun t => piece_le_psi ⟨1461,by decide +kernel⟩ t)
def piece1704 : AffinePiece := pieces[1462]'(by decide +kernel)
theorem intervalAccepted1704 : candidateIntervalCheck candidate1704 (4313/5000) (8627/10000) piece1704=true := by decide +kernel
noncomputable def cell1704 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1704 accepted1704 (4313/5000) (8627/10000) piece1704
    intervalAccepted1704 (fun t => piece_le_psi ⟨1462,by decide +kernel⟩ t)
def piece1705 : AffinePiece := pieces[1463]'(by decide +kernel)
theorem intervalAccepted1705 : candidateIntervalCheck candidate1705 (8627/10000) (2157/2500) piece1705=true := by decide +kernel
noncomputable def cell1705 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1705 accepted1705 (8627/10000) (2157/2500) piece1705
    intervalAccepted1705 (fun t => piece_le_psi ⟨1463,by decide +kernel⟩ t)
def piece1706 : AffinePiece := pieces[1464]'(by decide +kernel)
theorem intervalAccepted1706 : candidateIntervalCheck candidate1706 (2157/2500) (8629/10000) piece1706=true := by decide +kernel
noncomputable def cell1706 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1706 accepted1706 (2157/2500) (8629/10000) piece1706
    intervalAccepted1706 (fun t => piece_le_psi ⟨1464,by decide +kernel⟩ t)
def piece1707 : AffinePiece := pieces[1465]'(by decide +kernel)
theorem intervalAccepted1707 : candidateIntervalCheck candidate1707 (8629/10000) (863/1000) piece1707=true := by decide +kernel
noncomputable def cell1707 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1707 accepted1707 (8629/10000) (863/1000) piece1707
    intervalAccepted1707 (fun t => piece_le_psi ⟨1465,by decide +kernel⟩ t)
def piece1708 : AffinePiece := pieces[1466]'(by decide +kernel)
theorem intervalAccepted1708 : candidateIntervalCheck candidate1708 (863/1000) (8631/10000) piece1708=true := by decide +kernel
noncomputable def cell1708 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1708 accepted1708 (863/1000) (8631/10000) piece1708
    intervalAccepted1708 (fun t => piece_le_psi ⟨1466,by decide +kernel⟩ t)
def piece1709 : AffinePiece := pieces[1467]'(by decide +kernel)
theorem intervalAccepted1709 : candidateIntervalCheck candidate1709 (8631/10000) (1079/1250) piece1709=true := by decide +kernel
noncomputable def cell1709 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1709 accepted1709 (8631/10000) (1079/1250) piece1709
    intervalAccepted1709 (fun t => piece_le_psi ⟨1467,by decide +kernel⟩ t)
def piece1710 : AffinePiece := pieces[1468]'(by decide +kernel)
theorem intervalAccepted1710 : candidateIntervalCheck candidate1710 (1079/1250) (8633/10000) piece1710=true := by decide +kernel
noncomputable def cell1710 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1710 accepted1710 (1079/1250) (8633/10000) piece1710
    intervalAccepted1710 (fun t => piece_le_psi ⟨1468,by decide +kernel⟩ t)
def piece1711 : AffinePiece := pieces[1469]'(by decide +kernel)
theorem intervalAccepted1711 : candidateIntervalCheck candidate1711 (8633/10000) (4317/5000) piece1711=true := by decide +kernel
noncomputable def cell1711 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1711 accepted1711 (8633/10000) (4317/5000) piece1711
    intervalAccepted1711 (fun t => piece_le_psi ⟨1469,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1696, cell1697, cell1698, cell1699, cell1700, cell1701, cell1702, cell1703, cell1704, cell1705, cell1706, cell1707, cell1708, cell1709, cell1710, cell1711]
theorem chainAccepted : spinCellChainCheck (4309/5000) (4317/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4309/5000) (4317/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0106
