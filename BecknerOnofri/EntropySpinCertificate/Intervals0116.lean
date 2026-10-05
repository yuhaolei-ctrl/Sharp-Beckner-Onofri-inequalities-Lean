module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0116

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0116
open CandidateBatch0116 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1856 : AffinePiece := pieces[1500]'(by decide +kernel)
theorem intervalAccepted1856 : candidateIntervalCheck candidate1856 (889/1000) (1779/2000) piece1856=true := by decide +kernel
noncomputable def cell1856 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1856 accepted1856 (889/1000) (1779/2000) piece1856
    intervalAccepted1856 (fun t => piece_le_psi ⟨1500,by decide +kernel⟩ t)
def piece1857 : AffinePiece := pieces[1501]'(by decide +kernel)
theorem intervalAccepted1857 : candidateIntervalCheck candidate1857 (1779/2000) (89/100) piece1857=true := by decide +kernel
noncomputable def cell1857 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1857 accepted1857 (1779/2000) (89/100) piece1857
    intervalAccepted1857 (fun t => piece_le_psi ⟨1501,by decide +kernel⟩ t)
def piece1858 : AffinePiece := pieces[1502]'(by decide +kernel)
theorem intervalAccepted1858 : candidateIntervalCheck candidate1858 (89/100) (1781/2000) piece1858=true := by decide +kernel
noncomputable def cell1858 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1858 accepted1858 (89/100) (1781/2000) piece1858
    intervalAccepted1858 (fun t => piece_le_psi ⟨1502,by decide +kernel⟩ t)
def piece1859 : AffinePiece := pieces[1503]'(by decide +kernel)
theorem intervalAccepted1859 : candidateIntervalCheck candidate1859 (1781/2000) (891/1000) piece1859=true := by decide +kernel
noncomputable def cell1859 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1859 accepted1859 (1781/2000) (891/1000) piece1859
    intervalAccepted1859 (fun t => piece_le_psi ⟨1503,by decide +kernel⟩ t)
def piece1860 : AffinePiece := pieces[1504]'(by decide +kernel)
theorem intervalAccepted1860 : candidateIntervalCheck candidate1860 (891/1000) (1783/2000) piece1860=true := by decide +kernel
noncomputable def cell1860 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1860 accepted1860 (891/1000) (1783/2000) piece1860
    intervalAccepted1860 (fun t => piece_le_psi ⟨1504,by decide +kernel⟩ t)
def piece1861 : AffinePiece := pieces[1505]'(by decide +kernel)
theorem intervalAccepted1861 : candidateIntervalCheck candidate1861 (1783/2000) (223/250) piece1861=true := by decide +kernel
noncomputable def cell1861 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1861 accepted1861 (1783/2000) (223/250) piece1861
    intervalAccepted1861 (fun t => piece_le_psi ⟨1505,by decide +kernel⟩ t)
def piece1862 : AffinePiece := pieces[1506]'(by decide +kernel)
theorem intervalAccepted1862 : candidateIntervalCheck candidate1862 (223/250) (357/400) piece1862=true := by decide +kernel
noncomputable def cell1862 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1862 accepted1862 (223/250) (357/400) piece1862
    intervalAccepted1862 (fun t => piece_le_psi ⟨1506,by decide +kernel⟩ t)
def piece1863 : AffinePiece := pieces[1507]'(by decide +kernel)
theorem intervalAccepted1863 : candidateIntervalCheck candidate1863 (357/400) (893/1000) piece1863=true := by decide +kernel
noncomputable def cell1863 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1863 accepted1863 (357/400) (893/1000) piece1863
    intervalAccepted1863 (fun t => piece_le_psi ⟨1507,by decide +kernel⟩ t)
def piece1864 : AffinePiece := pieces[1508]'(by decide +kernel)
theorem intervalAccepted1864 : candidateIntervalCheck candidate1864 (893/1000) (1787/2000) piece1864=true := by decide +kernel
noncomputable def cell1864 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1864 accepted1864 (893/1000) (1787/2000) piece1864
    intervalAccepted1864 (fun t => piece_le_psi ⟨1508,by decide +kernel⟩ t)
def piece1865 : AffinePiece := pieces[1509]'(by decide +kernel)
theorem intervalAccepted1865 : candidateIntervalCheck candidate1865 (1787/2000) (447/500) piece1865=true := by decide +kernel
noncomputable def cell1865 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1865 accepted1865 (1787/2000) (447/500) piece1865
    intervalAccepted1865 (fun t => piece_le_psi ⟨1509,by decide +kernel⟩ t)
def piece1866 : AffinePiece := pieces[1510]'(by decide +kernel)
theorem intervalAccepted1866 : candidateIntervalCheck candidate1866 (447/500) (1789/2000) piece1866=true := by decide +kernel
noncomputable def cell1866 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1866 accepted1866 (447/500) (1789/2000) piece1866
    intervalAccepted1866 (fun t => piece_le_psi ⟨1510,by decide +kernel⟩ t)
def piece1867 : AffinePiece := pieces[1511]'(by decide +kernel)
theorem intervalAccepted1867 : candidateIntervalCheck candidate1867 (1789/2000) (179/200) piece1867=true := by decide +kernel
noncomputable def cell1867 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1867 accepted1867 (1789/2000) (179/200) piece1867
    intervalAccepted1867 (fun t => piece_le_psi ⟨1511,by decide +kernel⟩ t)
def piece1868 : AffinePiece := pieces[1512]'(by decide +kernel)
theorem intervalAccepted1868 : candidateIntervalCheck candidate1868 (179/200) (1791/2000) piece1868=true := by decide +kernel
noncomputable def cell1868 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1868 accepted1868 (179/200) (1791/2000) piece1868
    intervalAccepted1868 (fun t => piece_le_psi ⟨1512,by decide +kernel⟩ t)
def piece1869 : AffinePiece := pieces[1513]'(by decide +kernel)
theorem intervalAccepted1869 : candidateIntervalCheck candidate1869 (1791/2000) (112/125) piece1869=true := by decide +kernel
noncomputable def cell1869 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1869 accepted1869 (1791/2000) (112/125) piece1869
    intervalAccepted1869 (fun t => piece_le_psi ⟨1513,by decide +kernel⟩ t)
def piece1870 : AffinePiece := pieces[1514]'(by decide +kernel)
theorem intervalAccepted1870 : candidateIntervalCheck candidate1870 (112/125) (1793/2000) piece1870=true := by decide +kernel
noncomputable def cell1870 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1870 accepted1870 (112/125) (1793/2000) piece1870
    intervalAccepted1870 (fun t => piece_le_psi ⟨1514,by decide +kernel⟩ t)
def piece1871 : AffinePiece := pieces[1515]'(by decide +kernel)
theorem intervalAccepted1871 : candidateIntervalCheck candidate1871 (1793/2000) (897/1000) piece1871=true := by decide +kernel
noncomputable def cell1871 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1871 accepted1871 (1793/2000) (897/1000) piece1871
    intervalAccepted1871 (fun t => piece_le_psi ⟨1515,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1856, cell1857, cell1858, cell1859, cell1860, cell1861, cell1862, cell1863, cell1864, cell1865, cell1866, cell1867, cell1868, cell1869, cell1870, cell1871]
theorem chainAccepted : spinCellChainCheck (889/1000) (897/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (889/1000) (897/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0116
