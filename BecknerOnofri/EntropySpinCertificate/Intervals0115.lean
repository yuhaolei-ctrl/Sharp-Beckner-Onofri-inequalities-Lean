module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0115

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0115
open CandidateBatch0115 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1840 : AffinePiece := pieces[1484]'(by decide +kernel)
theorem intervalAccepted1840 : candidateIntervalCheck candidate1840 (881/1000) (1763/2000) piece1840=true := by decide +kernel
noncomputable def cell1840 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1840 accepted1840 (881/1000) (1763/2000) piece1840
    intervalAccepted1840 (fun t => piece_le_psi ⟨1484,by decide +kernel⟩ t)
def piece1841 : AffinePiece := pieces[1485]'(by decide +kernel)
theorem intervalAccepted1841 : candidateIntervalCheck candidate1841 (1763/2000) (441/500) piece1841=true := by decide +kernel
noncomputable def cell1841 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1841 accepted1841 (1763/2000) (441/500) piece1841
    intervalAccepted1841 (fun t => piece_le_psi ⟨1485,by decide +kernel⟩ t)
def piece1842 : AffinePiece := pieces[1486]'(by decide +kernel)
theorem intervalAccepted1842 : candidateIntervalCheck candidate1842 (441/500) (353/400) piece1842=true := by decide +kernel
noncomputable def cell1842 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1842 accepted1842 (441/500) (353/400) piece1842
    intervalAccepted1842 (fun t => piece_le_psi ⟨1486,by decide +kernel⟩ t)
def piece1843 : AffinePiece := pieces[1487]'(by decide +kernel)
theorem intervalAccepted1843 : candidateIntervalCheck candidate1843 (353/400) (883/1000) piece1843=true := by decide +kernel
noncomputable def cell1843 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1843 accepted1843 (353/400) (883/1000) piece1843
    intervalAccepted1843 (fun t => piece_le_psi ⟨1487,by decide +kernel⟩ t)
def piece1844 : AffinePiece := pieces[1488]'(by decide +kernel)
theorem intervalAccepted1844 : candidateIntervalCheck candidate1844 (883/1000) (1767/2000) piece1844=true := by decide +kernel
noncomputable def cell1844 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1844 accepted1844 (883/1000) (1767/2000) piece1844
    intervalAccepted1844 (fun t => piece_le_psi ⟨1488,by decide +kernel⟩ t)
def piece1845 : AffinePiece := pieces[1489]'(by decide +kernel)
theorem intervalAccepted1845 : candidateIntervalCheck candidate1845 (1767/2000) (221/250) piece1845=true := by decide +kernel
noncomputable def cell1845 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1845 accepted1845 (1767/2000) (221/250) piece1845
    intervalAccepted1845 (fun t => piece_le_psi ⟨1489,by decide +kernel⟩ t)
def piece1846 : AffinePiece := pieces[1490]'(by decide +kernel)
theorem intervalAccepted1846 : candidateIntervalCheck candidate1846 (221/250) (1769/2000) piece1846=true := by decide +kernel
noncomputable def cell1846 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1846 accepted1846 (221/250) (1769/2000) piece1846
    intervalAccepted1846 (fun t => piece_le_psi ⟨1490,by decide +kernel⟩ t)
def piece1847 : AffinePiece := pieces[1491]'(by decide +kernel)
theorem intervalAccepted1847 : candidateIntervalCheck candidate1847 (1769/2000) (177/200) piece1847=true := by decide +kernel
noncomputable def cell1847 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1847 accepted1847 (1769/2000) (177/200) piece1847
    intervalAccepted1847 (fun t => piece_le_psi ⟨1491,by decide +kernel⟩ t)
def piece1848 : AffinePiece := pieces[1492]'(by decide +kernel)
theorem intervalAccepted1848 : candidateIntervalCheck candidate1848 (177/200) (1771/2000) piece1848=true := by decide +kernel
noncomputable def cell1848 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1848 accepted1848 (177/200) (1771/2000) piece1848
    intervalAccepted1848 (fun t => piece_le_psi ⟨1492,by decide +kernel⟩ t)
def piece1849 : AffinePiece := pieces[1493]'(by decide +kernel)
theorem intervalAccepted1849 : candidateIntervalCheck candidate1849 (1771/2000) (443/500) piece1849=true := by decide +kernel
noncomputable def cell1849 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1849 accepted1849 (1771/2000) (443/500) piece1849
    intervalAccepted1849 (fun t => piece_le_psi ⟨1493,by decide +kernel⟩ t)
def piece1850 : AffinePiece := pieces[1494]'(by decide +kernel)
theorem intervalAccepted1850 : candidateIntervalCheck candidate1850 (443/500) (1773/2000) piece1850=true := by decide +kernel
noncomputable def cell1850 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1850 accepted1850 (443/500) (1773/2000) piece1850
    intervalAccepted1850 (fun t => piece_le_psi ⟨1494,by decide +kernel⟩ t)
def piece1851 : AffinePiece := pieces[1495]'(by decide +kernel)
theorem intervalAccepted1851 : candidateIntervalCheck candidate1851 (1773/2000) (887/1000) piece1851=true := by decide +kernel
noncomputable def cell1851 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1851 accepted1851 (1773/2000) (887/1000) piece1851
    intervalAccepted1851 (fun t => piece_le_psi ⟨1495,by decide +kernel⟩ t)
def piece1852 : AffinePiece := pieces[1496]'(by decide +kernel)
theorem intervalAccepted1852 : candidateIntervalCheck candidate1852 (887/1000) (71/80) piece1852=true := by decide +kernel
noncomputable def cell1852 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1852 accepted1852 (887/1000) (71/80) piece1852
    intervalAccepted1852 (fun t => piece_le_psi ⟨1496,by decide +kernel⟩ t)
def piece1853 : AffinePiece := pieces[1497]'(by decide +kernel)
theorem intervalAccepted1853 : candidateIntervalCheck candidate1853 (71/80) (111/125) piece1853=true := by decide +kernel
noncomputable def cell1853 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1853 accepted1853 (71/80) (111/125) piece1853
    intervalAccepted1853 (fun t => piece_le_psi ⟨1497,by decide +kernel⟩ t)
def piece1854 : AffinePiece := pieces[1498]'(by decide +kernel)
theorem intervalAccepted1854 : candidateIntervalCheck candidate1854 (111/125) (1777/2000) piece1854=true := by decide +kernel
noncomputable def cell1854 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1854 accepted1854 (111/125) (1777/2000) piece1854
    intervalAccepted1854 (fun t => piece_le_psi ⟨1498,by decide +kernel⟩ t)
def piece1855 : AffinePiece := pieces[1499]'(by decide +kernel)
theorem intervalAccepted1855 : candidateIntervalCheck candidate1855 (1777/2000) (889/1000) piece1855=true := by decide +kernel
noncomputable def cell1855 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1855 accepted1855 (1777/2000) (889/1000) piece1855
    intervalAccepted1855 (fun t => piece_le_psi ⟨1499,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1840, cell1841, cell1842, cell1843, cell1844, cell1845, cell1846, cell1847, cell1848, cell1849, cell1850, cell1851, cell1852, cell1853, cell1854, cell1855]
theorem chainAccepted : spinCellChainCheck (881/1000) (889/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (881/1000) (889/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0115
