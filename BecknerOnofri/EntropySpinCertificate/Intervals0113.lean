module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0113

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0113
open CandidateBatch0113 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1808 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1808 : candidateIntervalCheck candidate1808 (873/1000) (8731/10000) piece1808=true := by decide +kernel
noncomputable def cell1808 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1808 accepted1808 (873/1000) (8731/10000) piece1808
    intervalAccepted1808 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1809 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1809 : candidateIntervalCheck candidate1809 (8731/10000) (2183/2500) piece1809=true := by decide +kernel
noncomputable def cell1809 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1809 accepted1809 (8731/10000) (2183/2500) piece1809
    intervalAccepted1809 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1810 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1810 : candidateIntervalCheck candidate1810 (2183/2500) (8733/10000) piece1810=true := by decide +kernel
noncomputable def cell1810 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1810 accepted1810 (2183/2500) (8733/10000) piece1810
    intervalAccepted1810 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1811 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1811 : candidateIntervalCheck candidate1811 (8733/10000) (4367/5000) piece1811=true := by decide +kernel
noncomputable def cell1811 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1811 accepted1811 (8733/10000) (4367/5000) piece1811
    intervalAccepted1811 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1812 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1812 : candidateIntervalCheck candidate1812 (4367/5000) (1747/2000) piece1812=true := by decide +kernel
noncomputable def cell1812 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1812 accepted1812 (4367/5000) (1747/2000) piece1812
    intervalAccepted1812 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1813 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1813 : candidateIntervalCheck candidate1813 (1747/2000) (546/625) piece1813=true := by decide +kernel
noncomputable def cell1813 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1813 accepted1813 (1747/2000) (546/625) piece1813
    intervalAccepted1813 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1814 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1814 : candidateIntervalCheck candidate1814 (546/625) (8737/10000) piece1814=true := by decide +kernel
noncomputable def cell1814 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1814 accepted1814 (546/625) (8737/10000) piece1814
    intervalAccepted1814 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1815 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1815 : candidateIntervalCheck candidate1815 (8737/10000) (4369/5000) piece1815=true := by decide +kernel
noncomputable def cell1815 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1815 accepted1815 (8737/10000) (4369/5000) piece1815
    intervalAccepted1815 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1816 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1816 : candidateIntervalCheck candidate1816 (4369/5000) (8739/10000) piece1816=true := by decide +kernel
noncomputable def cell1816 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1816 accepted1816 (4369/5000) (8739/10000) piece1816
    intervalAccepted1816 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1817 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1817 : candidateIntervalCheck candidate1817 (8739/10000) (437/500) piece1817=true := by decide +kernel
noncomputable def cell1817 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1817 accepted1817 (8739/10000) (437/500) piece1817
    intervalAccepted1817 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1818 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1818 : candidateIntervalCheck candidate1818 (437/500) (8741/10000) piece1818=true := by decide +kernel
noncomputable def cell1818 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1818 accepted1818 (437/500) (8741/10000) piece1818
    intervalAccepted1818 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1819 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1819 : candidateIntervalCheck candidate1819 (8741/10000) (4371/5000) piece1819=true := by decide +kernel
noncomputable def cell1819 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1819 accepted1819 (8741/10000) (4371/5000) piece1819
    intervalAccepted1819 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1820 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1820 : candidateIntervalCheck candidate1820 (4371/5000) (8743/10000) piece1820=true := by decide +kernel
noncomputable def cell1820 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1820 accepted1820 (4371/5000) (8743/10000) piece1820
    intervalAccepted1820 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1821 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1821 : candidateIntervalCheck candidate1821 (8743/10000) (1093/1250) piece1821=true := by decide +kernel
noncomputable def cell1821 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1821 accepted1821 (8743/10000) (1093/1250) piece1821
    intervalAccepted1821 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1822 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1822 : candidateIntervalCheck candidate1822 (1093/1250) (1749/2000) piece1822=true := by decide +kernel
noncomputable def cell1822 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1822 accepted1822 (1093/1250) (1749/2000) piece1822
    intervalAccepted1822 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1823 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1823 : candidateIntervalCheck candidate1823 (1749/2000) (4373/5000) piece1823=true := by decide +kernel
noncomputable def cell1823 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1823 accepted1823 (1749/2000) (4373/5000) piece1823
    intervalAccepted1823 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1808, cell1809, cell1810, cell1811, cell1812, cell1813, cell1814, cell1815, cell1816, cell1817, cell1818, cell1819, cell1820, cell1821, cell1822, cell1823]
theorem chainAccepted : spinCellChainCheck (873/1000) (4373/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (873/1000) (4373/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0113
