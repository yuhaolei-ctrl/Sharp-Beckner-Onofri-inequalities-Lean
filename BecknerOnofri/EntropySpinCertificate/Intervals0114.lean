import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0114
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0114
open CandidateBatch0114 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1824 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1824 : candidateIntervalCheck candidate1824 (4373/5000) (8747/10000) piece1824=true := by decide +kernel
noncomputable def cell1824 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1824 accepted1824 (4373/5000) (8747/10000) piece1824
    intervalAccepted1824 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1825 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1825 : candidateIntervalCheck candidate1825 (8747/10000) (2187/2500) piece1825=true := by decide +kernel
noncomputable def cell1825 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1825 accepted1825 (8747/10000) (2187/2500) piece1825
    intervalAccepted1825 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1826 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1826 : candidateIntervalCheck candidate1826 (2187/2500) (8749/10000) piece1826=true := by decide +kernel
noncomputable def cell1826 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1826 accepted1826 (2187/2500) (8749/10000) piece1826
    intervalAccepted1826 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1827 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1827 : candidateIntervalCheck candidate1827 (8749/10000) (7/8) piece1827=true := by decide +kernel
noncomputable def cell1827 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1827 accepted1827 (8749/10000) (7/8) piece1827
    intervalAccepted1827 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1828 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1828 : candidateIntervalCheck candidate1828 (7/8) (1751/2000) piece1828=true := by decide +kernel
noncomputable def cell1828 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1828 accepted1828 (7/8) (1751/2000) piece1828
    intervalAccepted1828 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1829 : AffinePiece := pieces[1473]'(by decide +kernel)
theorem intervalAccepted1829 : candidateIntervalCheck candidate1829 (1751/2000) (219/250) piece1829=true := by decide +kernel
noncomputable def cell1829 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1829 accepted1829 (1751/2000) (219/250) piece1829
    intervalAccepted1829 (fun t => piece_le_psi ⟨1473,by decide +kernel⟩ t)
def piece1830 : AffinePiece := pieces[1474]'(by decide +kernel)
theorem intervalAccepted1830 : candidateIntervalCheck candidate1830 (219/250) (1753/2000) piece1830=true := by decide +kernel
noncomputable def cell1830 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1830 accepted1830 (219/250) (1753/2000) piece1830
    intervalAccepted1830 (fun t => piece_le_psi ⟨1474,by decide +kernel⟩ t)
def piece1831 : AffinePiece := pieces[1475]'(by decide +kernel)
theorem intervalAccepted1831 : candidateIntervalCheck candidate1831 (1753/2000) (877/1000) piece1831=true := by decide +kernel
noncomputable def cell1831 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1831 accepted1831 (1753/2000) (877/1000) piece1831
    intervalAccepted1831 (fun t => piece_le_psi ⟨1475,by decide +kernel⟩ t)
def piece1832 : AffinePiece := pieces[1476]'(by decide +kernel)
theorem intervalAccepted1832 : candidateIntervalCheck candidate1832 (877/1000) (351/400) piece1832=true := by decide +kernel
noncomputable def cell1832 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1832 accepted1832 (877/1000) (351/400) piece1832
    intervalAccepted1832 (fun t => piece_le_psi ⟨1476,by decide +kernel⟩ t)
def piece1833 : AffinePiece := pieces[1477]'(by decide +kernel)
theorem intervalAccepted1833 : candidateIntervalCheck candidate1833 (351/400) (439/500) piece1833=true := by decide +kernel
noncomputable def cell1833 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1833 accepted1833 (351/400) (439/500) piece1833
    intervalAccepted1833 (fun t => piece_le_psi ⟨1477,by decide +kernel⟩ t)
def piece1834 : AffinePiece := pieces[1478]'(by decide +kernel)
theorem intervalAccepted1834 : candidateIntervalCheck candidate1834 (439/500) (1757/2000) piece1834=true := by decide +kernel
noncomputable def cell1834 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1834 accepted1834 (439/500) (1757/2000) piece1834
    intervalAccepted1834 (fun t => piece_le_psi ⟨1478,by decide +kernel⟩ t)
def piece1835 : AffinePiece := pieces[1479]'(by decide +kernel)
theorem intervalAccepted1835 : candidateIntervalCheck candidate1835 (1757/2000) (879/1000) piece1835=true := by decide +kernel
noncomputable def cell1835 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1835 accepted1835 (1757/2000) (879/1000) piece1835
    intervalAccepted1835 (fun t => piece_le_psi ⟨1479,by decide +kernel⟩ t)
def piece1836 : AffinePiece := pieces[1480]'(by decide +kernel)
theorem intervalAccepted1836 : candidateIntervalCheck candidate1836 (879/1000) (1759/2000) piece1836=true := by decide +kernel
noncomputable def cell1836 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1836 accepted1836 (879/1000) (1759/2000) piece1836
    intervalAccepted1836 (fun t => piece_le_psi ⟨1480,by decide +kernel⟩ t)
def piece1837 : AffinePiece := pieces[1481]'(by decide +kernel)
theorem intervalAccepted1837 : candidateIntervalCheck candidate1837 (1759/2000) (22/25) piece1837=true := by decide +kernel
noncomputable def cell1837 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1837 accepted1837 (1759/2000) (22/25) piece1837
    intervalAccepted1837 (fun t => piece_le_psi ⟨1481,by decide +kernel⟩ t)
def piece1838 : AffinePiece := pieces[1482]'(by decide +kernel)
theorem intervalAccepted1838 : candidateIntervalCheck candidate1838 (22/25) (1761/2000) piece1838=true := by decide +kernel
noncomputable def cell1838 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1838 accepted1838 (22/25) (1761/2000) piece1838
    intervalAccepted1838 (fun t => piece_le_psi ⟨1482,by decide +kernel⟩ t)
def piece1839 : AffinePiece := pieces[1483]'(by decide +kernel)
theorem intervalAccepted1839 : candidateIntervalCheck candidate1839 (1761/2000) (881/1000) piece1839=true := by decide +kernel
noncomputable def cell1839 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1839 accepted1839 (1761/2000) (881/1000) piece1839
    intervalAccepted1839 (fun t => piece_le_psi ⟨1483,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1824, cell1825, cell1826, cell1827, cell1828, cell1829, cell1830, cell1831, cell1832, cell1833, cell1834, cell1835, cell1836, cell1837, cell1838, cell1839]
theorem chainAccepted : spinCellChainCheck (4373/5000) (881/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4373/5000) (881/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0114
