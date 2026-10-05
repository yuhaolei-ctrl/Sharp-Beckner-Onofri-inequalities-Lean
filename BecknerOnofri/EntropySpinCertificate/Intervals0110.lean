import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0110
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0110
open CandidateBatch0110 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1760 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1760 : candidateIntervalCheck candidate1760 (4341/5000) (8683/10000) piece1760=true := by decide +kernel
noncomputable def cell1760 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1760 accepted1760 (4341/5000) (8683/10000) piece1760
    intervalAccepted1760 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1761 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1761 : candidateIntervalCheck candidate1761 (8683/10000) (2171/2500) piece1761=true := by decide +kernel
noncomputable def cell1761 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1761 accepted1761 (8683/10000) (2171/2500) piece1761
    intervalAccepted1761 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1762 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1762 : candidateIntervalCheck candidate1762 (2171/2500) (1737/2000) piece1762=true := by decide +kernel
noncomputable def cell1762 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1762 accepted1762 (2171/2500) (1737/2000) piece1762
    intervalAccepted1762 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1763 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1763 : candidateIntervalCheck candidate1763 (1737/2000) (4343/5000) piece1763=true := by decide +kernel
noncomputable def cell1763 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1763 accepted1763 (1737/2000) (4343/5000) piece1763
    intervalAccepted1763 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1764 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1764 : candidateIntervalCheck candidate1764 (4343/5000) (8687/10000) piece1764=true := by decide +kernel
noncomputable def cell1764 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1764 accepted1764 (4343/5000) (8687/10000) piece1764
    intervalAccepted1764 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1765 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1765 : candidateIntervalCheck candidate1765 (8687/10000) (543/625) piece1765=true := by decide +kernel
noncomputable def cell1765 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1765 accepted1765 (8687/10000) (543/625) piece1765
    intervalAccepted1765 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1766 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1766 : candidateIntervalCheck candidate1766 (543/625) (8689/10000) piece1766=true := by decide +kernel
noncomputable def cell1766 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1766 accepted1766 (543/625) (8689/10000) piece1766
    intervalAccepted1766 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1767 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1767 : candidateIntervalCheck candidate1767 (8689/10000) (869/1000) piece1767=true := by decide +kernel
noncomputable def cell1767 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1767 accepted1767 (8689/10000) (869/1000) piece1767
    intervalAccepted1767 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1768 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1768 : candidateIntervalCheck candidate1768 (869/1000) (8691/10000) piece1768=true := by decide +kernel
noncomputable def cell1768 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1768 accepted1768 (869/1000) (8691/10000) piece1768
    intervalAccepted1768 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1769 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1769 : candidateIntervalCheck candidate1769 (8691/10000) (2173/2500) piece1769=true := by decide +kernel
noncomputable def cell1769 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1769 accepted1769 (8691/10000) (2173/2500) piece1769
    intervalAccepted1769 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1770 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1770 : candidateIntervalCheck candidate1770 (2173/2500) (8693/10000) piece1770=true := by decide +kernel
noncomputable def cell1770 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1770 accepted1770 (2173/2500) (8693/10000) piece1770
    intervalAccepted1770 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1771 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1771 : candidateIntervalCheck candidate1771 (8693/10000) (4347/5000) piece1771=true := by decide +kernel
noncomputable def cell1771 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1771 accepted1771 (8693/10000) (4347/5000) piece1771
    intervalAccepted1771 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1772 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1772 : candidateIntervalCheck candidate1772 (4347/5000) (1739/2000) piece1772=true := by decide +kernel
noncomputable def cell1772 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1772 accepted1772 (4347/5000) (1739/2000) piece1772
    intervalAccepted1772 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1773 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1773 : candidateIntervalCheck candidate1773 (1739/2000) (1087/1250) piece1773=true := by decide +kernel
noncomputable def cell1773 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1773 accepted1773 (1739/2000) (1087/1250) piece1773
    intervalAccepted1773 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1774 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1774 : candidateIntervalCheck candidate1774 (1087/1250) (8697/10000) piece1774=true := by decide +kernel
noncomputable def cell1774 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1774 accepted1774 (1087/1250) (8697/10000) piece1774
    intervalAccepted1774 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1775 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1775 : candidateIntervalCheck candidate1775 (8697/10000) (4349/5000) piece1775=true := by decide +kernel
noncomputable def cell1775 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1775 accepted1775 (8697/10000) (4349/5000) piece1775
    intervalAccepted1775 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1760, cell1761, cell1762, cell1763, cell1764, cell1765, cell1766, cell1767, cell1768, cell1769, cell1770, cell1771, cell1772, cell1773, cell1774, cell1775]
theorem chainAccepted : spinCellChainCheck (4341/5000) (4349/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4341/5000) (4349/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0110
