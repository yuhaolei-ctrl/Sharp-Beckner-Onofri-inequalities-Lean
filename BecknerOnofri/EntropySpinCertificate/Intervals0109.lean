import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0109
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0109
open CandidateBatch0109 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1744 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1744 : candidateIntervalCheck candidate1744 (4333/5000) (8667/10000) piece1744=true := by decide +kernel
noncomputable def cell1744 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1744 accepted1744 (4333/5000) (8667/10000) piece1744
    intervalAccepted1744 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1745 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1745 : candidateIntervalCheck candidate1745 (8667/10000) (2167/2500) piece1745=true := by decide +kernel
noncomputable def cell1745 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1745 accepted1745 (8667/10000) (2167/2500) piece1745
    intervalAccepted1745 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1746 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1746 : candidateIntervalCheck candidate1746 (2167/2500) (8669/10000) piece1746=true := by decide +kernel
noncomputable def cell1746 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1746 accepted1746 (2167/2500) (8669/10000) piece1746
    intervalAccepted1746 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1747 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1747 : candidateIntervalCheck candidate1747 (8669/10000) (867/1000) piece1747=true := by decide +kernel
noncomputable def cell1747 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1747 accepted1747 (8669/10000) (867/1000) piece1747
    intervalAccepted1747 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1748 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1748 : candidateIntervalCheck candidate1748 (867/1000) (8671/10000) piece1748=true := by decide +kernel
noncomputable def cell1748 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1748 accepted1748 (867/1000) (8671/10000) piece1748
    intervalAccepted1748 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1749 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1749 : candidateIntervalCheck candidate1749 (8671/10000) (542/625) piece1749=true := by decide +kernel
noncomputable def cell1749 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1749 accepted1749 (8671/10000) (542/625) piece1749
    intervalAccepted1749 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1750 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1750 : candidateIntervalCheck candidate1750 (542/625) (8673/10000) piece1750=true := by decide +kernel
noncomputable def cell1750 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1750 accepted1750 (542/625) (8673/10000) piece1750
    intervalAccepted1750 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1751 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1751 : candidateIntervalCheck candidate1751 (8673/10000) (4337/5000) piece1751=true := by decide +kernel
noncomputable def cell1751 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1751 accepted1751 (8673/10000) (4337/5000) piece1751
    intervalAccepted1751 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1752 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1752 : candidateIntervalCheck candidate1752 (4337/5000) (347/400) piece1752=true := by decide +kernel
noncomputable def cell1752 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1752 accepted1752 (4337/5000) (347/400) piece1752
    intervalAccepted1752 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1753 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1753 : candidateIntervalCheck candidate1753 (347/400) (2169/2500) piece1753=true := by decide +kernel
noncomputable def cell1753 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1753 accepted1753 (347/400) (2169/2500) piece1753
    intervalAccepted1753 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1754 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1754 : candidateIntervalCheck candidate1754 (2169/2500) (8677/10000) piece1754=true := by decide +kernel
noncomputable def cell1754 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1754 accepted1754 (2169/2500) (8677/10000) piece1754
    intervalAccepted1754 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1755 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1755 : candidateIntervalCheck candidate1755 (8677/10000) (4339/5000) piece1755=true := by decide +kernel
noncomputable def cell1755 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1755 accepted1755 (8677/10000) (4339/5000) piece1755
    intervalAccepted1755 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1756 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1756 : candidateIntervalCheck candidate1756 (4339/5000) (8679/10000) piece1756=true := by decide +kernel
noncomputable def cell1756 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1756 accepted1756 (4339/5000) (8679/10000) piece1756
    intervalAccepted1756 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1757 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1757 : candidateIntervalCheck candidate1757 (8679/10000) (217/250) piece1757=true := by decide +kernel
noncomputable def cell1757 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1757 accepted1757 (8679/10000) (217/250) piece1757
    intervalAccepted1757 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1758 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1758 : candidateIntervalCheck candidate1758 (217/250) (8681/10000) piece1758=true := by decide +kernel
noncomputable def cell1758 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1758 accepted1758 (217/250) (8681/10000) piece1758
    intervalAccepted1758 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1759 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1759 : candidateIntervalCheck candidate1759 (8681/10000) (4341/5000) piece1759=true := by decide +kernel
noncomputable def cell1759 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1759 accepted1759 (8681/10000) (4341/5000) piece1759
    intervalAccepted1759 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1744, cell1745, cell1746, cell1747, cell1748, cell1749, cell1750, cell1751, cell1752, cell1753, cell1754, cell1755, cell1756, cell1757, cell1758, cell1759]
theorem chainAccepted : spinCellChainCheck (4333/5000) (4341/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4333/5000) (4341/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0109
