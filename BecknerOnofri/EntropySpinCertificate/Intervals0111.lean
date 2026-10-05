import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0111
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0111
open CandidateBatch0111 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1776 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1776 : candidateIntervalCheck candidate1776 (4349/5000) (8699/10000) piece1776=true := by decide +kernel
noncomputable def cell1776 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1776 accepted1776 (4349/5000) (8699/10000) piece1776
    intervalAccepted1776 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1777 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1777 : candidateIntervalCheck candidate1777 (8699/10000) (87/100) piece1777=true := by decide +kernel
noncomputable def cell1777 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1777 accepted1777 (8699/10000) (87/100) piece1777
    intervalAccepted1777 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1778 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1778 : candidateIntervalCheck candidate1778 (87/100) (8701/10000) piece1778=true := by decide +kernel
noncomputable def cell1778 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1778 accepted1778 (87/100) (8701/10000) piece1778
    intervalAccepted1778 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1779 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1779 : candidateIntervalCheck candidate1779 (8701/10000) (4351/5000) piece1779=true := by decide +kernel
noncomputable def cell1779 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1779 accepted1779 (8701/10000) (4351/5000) piece1779
    intervalAccepted1779 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1780 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1780 : candidateIntervalCheck candidate1780 (4351/5000) (8703/10000) piece1780=true := by decide +kernel
noncomputable def cell1780 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1780 accepted1780 (4351/5000) (8703/10000) piece1780
    intervalAccepted1780 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1781 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1781 : candidateIntervalCheck candidate1781 (8703/10000) (544/625) piece1781=true := by decide +kernel
noncomputable def cell1781 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1781 accepted1781 (8703/10000) (544/625) piece1781
    intervalAccepted1781 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1782 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1782 : candidateIntervalCheck candidate1782 (544/625) (1741/2000) piece1782=true := by decide +kernel
noncomputable def cell1782 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1782 accepted1782 (544/625) (1741/2000) piece1782
    intervalAccepted1782 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1783 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1783 : candidateIntervalCheck candidate1783 (1741/2000) (4353/5000) piece1783=true := by decide +kernel
noncomputable def cell1783 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1783 accepted1783 (1741/2000) (4353/5000) piece1783
    intervalAccepted1783 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1784 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1784 : candidateIntervalCheck candidate1784 (4353/5000) (8707/10000) piece1784=true := by decide +kernel
noncomputable def cell1784 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1784 accepted1784 (4353/5000) (8707/10000) piece1784
    intervalAccepted1784 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1785 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1785 : candidateIntervalCheck candidate1785 (8707/10000) (2177/2500) piece1785=true := by decide +kernel
noncomputable def cell1785 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1785 accepted1785 (8707/10000) (2177/2500) piece1785
    intervalAccepted1785 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1786 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1786 : candidateIntervalCheck candidate1786 (2177/2500) (8709/10000) piece1786=true := by decide +kernel
noncomputable def cell1786 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1786 accepted1786 (2177/2500) (8709/10000) piece1786
    intervalAccepted1786 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1787 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1787 : candidateIntervalCheck candidate1787 (8709/10000) (871/1000) piece1787=true := by decide +kernel
noncomputable def cell1787 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1787 accepted1787 (8709/10000) (871/1000) piece1787
    intervalAccepted1787 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1788 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1788 : candidateIntervalCheck candidate1788 (871/1000) (8711/10000) piece1788=true := by decide +kernel
noncomputable def cell1788 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1788 accepted1788 (871/1000) (8711/10000) piece1788
    intervalAccepted1788 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1789 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1789 : candidateIntervalCheck candidate1789 (8711/10000) (1089/1250) piece1789=true := by decide +kernel
noncomputable def cell1789 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1789 accepted1789 (8711/10000) (1089/1250) piece1789
    intervalAccepted1789 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1790 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1790 : candidateIntervalCheck candidate1790 (1089/1250) (8713/10000) piece1790=true := by decide +kernel
noncomputable def cell1790 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1790 accepted1790 (1089/1250) (8713/10000) piece1790
    intervalAccepted1790 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1791 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1791 : candidateIntervalCheck candidate1791 (8713/10000) (4357/5000) piece1791=true := by decide +kernel
noncomputable def cell1791 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1791 accepted1791 (8713/10000) (4357/5000) piece1791
    intervalAccepted1791 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1776, cell1777, cell1778, cell1779, cell1780, cell1781, cell1782, cell1783, cell1784, cell1785, cell1786, cell1787, cell1788, cell1789, cell1790, cell1791]
theorem chainAccepted : spinCellChainCheck (4349/5000) (4357/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4349/5000) (4357/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0111
