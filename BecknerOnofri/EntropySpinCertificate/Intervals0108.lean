module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0108

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0108
open CandidateBatch0108 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1728 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1728 : candidateIntervalCheck candidate1728 (173/200) (8651/10000) piece1728=true := by decide +kernel
noncomputable def cell1728 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1728 accepted1728 (173/200) (8651/10000) piece1728
    intervalAccepted1728 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1729 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1729 : candidateIntervalCheck candidate1729 (8651/10000) (2163/2500) piece1729=true := by decide +kernel
noncomputable def cell1729 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1729 accepted1729 (8651/10000) (2163/2500) piece1729
    intervalAccepted1729 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1730 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1730 : candidateIntervalCheck candidate1730 (2163/2500) (8653/10000) piece1730=true := by decide +kernel
noncomputable def cell1730 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1730 accepted1730 (2163/2500) (8653/10000) piece1730
    intervalAccepted1730 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1731 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1731 : candidateIntervalCheck candidate1731 (8653/10000) (4327/5000) piece1731=true := by decide +kernel
noncomputable def cell1731 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1731 accepted1731 (8653/10000) (4327/5000) piece1731
    intervalAccepted1731 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1732 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1732 : candidateIntervalCheck candidate1732 (4327/5000) (1731/2000) piece1732=true := by decide +kernel
noncomputable def cell1732 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1732 accepted1732 (4327/5000) (1731/2000) piece1732
    intervalAccepted1732 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1733 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1733 : candidateIntervalCheck candidate1733 (1731/2000) (541/625) piece1733=true := by decide +kernel
noncomputable def cell1733 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1733 accepted1733 (1731/2000) (541/625) piece1733
    intervalAccepted1733 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1734 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1734 : candidateIntervalCheck candidate1734 (541/625) (8657/10000) piece1734=true := by decide +kernel
noncomputable def cell1734 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1734 accepted1734 (541/625) (8657/10000) piece1734
    intervalAccepted1734 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1735 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1735 : candidateIntervalCheck candidate1735 (8657/10000) (4329/5000) piece1735=true := by decide +kernel
noncomputable def cell1735 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1735 accepted1735 (8657/10000) (4329/5000) piece1735
    intervalAccepted1735 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1736 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1736 : candidateIntervalCheck candidate1736 (4329/5000) (8659/10000) piece1736=true := by decide +kernel
noncomputable def cell1736 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1736 accepted1736 (4329/5000) (8659/10000) piece1736
    intervalAccepted1736 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1737 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1737 : candidateIntervalCheck candidate1737 (8659/10000) (433/500) piece1737=true := by decide +kernel
noncomputable def cell1737 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1737 accepted1737 (8659/10000) (433/500) piece1737
    intervalAccepted1737 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1738 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1738 : candidateIntervalCheck candidate1738 (433/500) (8661/10000) piece1738=true := by decide +kernel
noncomputable def cell1738 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1738 accepted1738 (433/500) (8661/10000) piece1738
    intervalAccepted1738 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1739 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1739 : candidateIntervalCheck candidate1739 (8661/10000) (4331/5000) piece1739=true := by decide +kernel
noncomputable def cell1739 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1739 accepted1739 (8661/10000) (4331/5000) piece1739
    intervalAccepted1739 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1740 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1740 : candidateIntervalCheck candidate1740 (4331/5000) (8663/10000) piece1740=true := by decide +kernel
noncomputable def cell1740 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1740 accepted1740 (4331/5000) (8663/10000) piece1740
    intervalAccepted1740 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1741 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1741 : candidateIntervalCheck candidate1741 (8663/10000) (1083/1250) piece1741=true := by decide +kernel
noncomputable def cell1741 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1741 accepted1741 (8663/10000) (1083/1250) piece1741
    intervalAccepted1741 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1742 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1742 : candidateIntervalCheck candidate1742 (1083/1250) (1733/2000) piece1742=true := by decide +kernel
noncomputable def cell1742 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1742 accepted1742 (1083/1250) (1733/2000) piece1742
    intervalAccepted1742 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1743 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1743 : candidateIntervalCheck candidate1743 (1733/2000) (4333/5000) piece1743=true := by decide +kernel
noncomputable def cell1743 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1743 accepted1743 (1733/2000) (4333/5000) piece1743
    intervalAccepted1743 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1728, cell1729, cell1730, cell1731, cell1732, cell1733, cell1734, cell1735, cell1736, cell1737, cell1738, cell1739, cell1740, cell1741, cell1742, cell1743]
theorem chainAccepted : spinCellChainCheck (173/200) (4333/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (173/200) (4333/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0108
