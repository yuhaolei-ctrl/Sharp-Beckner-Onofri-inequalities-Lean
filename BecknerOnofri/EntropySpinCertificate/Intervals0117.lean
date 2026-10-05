import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0117
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0117
open CandidateBatch0117 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1872 : AffinePiece := pieces[1516]'(by decide +kernel)
theorem intervalAccepted1872 : candidateIntervalCheck candidate1872 (897/1000) (359/400) piece1872=true := by decide +kernel
noncomputable def cell1872 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1872 accepted1872 (897/1000) (359/400) piece1872
    intervalAccepted1872 (fun t => piece_le_psi ⟨1516,by decide +kernel⟩ t)
def piece1873 : AffinePiece := pieces[1517]'(by decide +kernel)
theorem intervalAccepted1873 : candidateIntervalCheck candidate1873 (359/400) (449/500) piece1873=true := by decide +kernel
noncomputable def cell1873 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1873 accepted1873 (359/400) (449/500) piece1873
    intervalAccepted1873 (fun t => piece_le_psi ⟨1517,by decide +kernel⟩ t)
def piece1874 : AffinePiece := pieces[1518]'(by decide +kernel)
theorem intervalAccepted1874 : candidateIntervalCheck candidate1874 (449/500) (1797/2000) piece1874=true := by decide +kernel
noncomputable def cell1874 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1874 accepted1874 (449/500) (1797/2000) piece1874
    intervalAccepted1874 (fun t => piece_le_psi ⟨1518,by decide +kernel⟩ t)
def piece1875 : AffinePiece := pieces[1519]'(by decide +kernel)
theorem intervalAccepted1875 : candidateIntervalCheck candidate1875 (1797/2000) (899/1000) piece1875=true := by decide +kernel
noncomputable def cell1875 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1875 accepted1875 (1797/2000) (899/1000) piece1875
    intervalAccepted1875 (fun t => piece_le_psi ⟨1519,by decide +kernel⟩ t)
def piece1876 : AffinePiece := pieces[1520]'(by decide +kernel)
theorem intervalAccepted1876 : candidateIntervalCheck candidate1876 (899/1000) (1799/2000) piece1876=true := by decide +kernel
noncomputable def cell1876 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1876 accepted1876 (899/1000) (1799/2000) piece1876
    intervalAccepted1876 (fun t => piece_le_psi ⟨1520,by decide +kernel⟩ t)
def piece1877 : AffinePiece := pieces[1521]'(by decide +kernel)
theorem intervalAccepted1877 : candidateIntervalCheck candidate1877 (1799/2000) (9/10) piece1877=true := by decide +kernel
noncomputable def cell1877 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1877 accepted1877 (1799/2000) (9/10) piece1877
    intervalAccepted1877 (fun t => piece_le_psi ⟨1521,by decide +kernel⟩ t)
def piece1878 : AffinePiece := pieces[1522]'(by decide +kernel)
theorem intervalAccepted1878 : candidateIntervalCheck candidate1878 (9/10) (1801/2000) piece1878=true := by decide +kernel
noncomputable def cell1878 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1878 accepted1878 (9/10) (1801/2000) piece1878
    intervalAccepted1878 (fun t => piece_le_psi ⟨1522,by decide +kernel⟩ t)
def piece1879 : AffinePiece := pieces[1523]'(by decide +kernel)
theorem intervalAccepted1879 : candidateIntervalCheck candidate1879 (1801/2000) (901/1000) piece1879=true := by decide +kernel
noncomputable def cell1879 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1879 accepted1879 (1801/2000) (901/1000) piece1879
    intervalAccepted1879 (fun t => piece_le_psi ⟨1523,by decide +kernel⟩ t)
def piece1880 : AffinePiece := pieces[1524]'(by decide +kernel)
theorem intervalAccepted1880 : candidateIntervalCheck candidate1880 (901/1000) (1803/2000) piece1880=true := by decide +kernel
noncomputable def cell1880 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1880 accepted1880 (901/1000) (1803/2000) piece1880
    intervalAccepted1880 (fun t => piece_le_psi ⟨1524,by decide +kernel⟩ t)
def piece1881 : AffinePiece := pieces[1525]'(by decide +kernel)
theorem intervalAccepted1881 : candidateIntervalCheck candidate1881 (1803/2000) (451/500) piece1881=true := by decide +kernel
noncomputable def cell1881 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1881 accepted1881 (1803/2000) (451/500) piece1881
    intervalAccepted1881 (fun t => piece_le_psi ⟨1525,by decide +kernel⟩ t)
def piece1882 : AffinePiece := pieces[1526]'(by decide +kernel)
theorem intervalAccepted1882 : candidateIntervalCheck candidate1882 (451/500) (361/400) piece1882=true := by decide +kernel
noncomputable def cell1882 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1882 accepted1882 (451/500) (361/400) piece1882
    intervalAccepted1882 (fun t => piece_le_psi ⟨1526,by decide +kernel⟩ t)
def piece1883 : AffinePiece := pieces[1527]'(by decide +kernel)
theorem intervalAccepted1883 : candidateIntervalCheck candidate1883 (361/400) (903/1000) piece1883=true := by decide +kernel
noncomputable def cell1883 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1883 accepted1883 (361/400) (903/1000) piece1883
    intervalAccepted1883 (fun t => piece_le_psi ⟨1527,by decide +kernel⟩ t)
def piece1884 : AffinePiece := pieces[1528]'(by decide +kernel)
theorem intervalAccepted1884 : candidateIntervalCheck candidate1884 (903/1000) (1807/2000) piece1884=true := by decide +kernel
noncomputable def cell1884 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1884 accepted1884 (903/1000) (1807/2000) piece1884
    intervalAccepted1884 (fun t => piece_le_psi ⟨1528,by decide +kernel⟩ t)
def piece1885 : AffinePiece := pieces[1529]'(by decide +kernel)
theorem intervalAccepted1885 : candidateIntervalCheck candidate1885 (1807/2000) (113/125) piece1885=true := by decide +kernel
noncomputable def cell1885 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1885 accepted1885 (1807/2000) (113/125) piece1885
    intervalAccepted1885 (fun t => piece_le_psi ⟨1529,by decide +kernel⟩ t)
def piece1886 : AffinePiece := pieces[1530]'(by decide +kernel)
theorem intervalAccepted1886 : candidateIntervalCheck candidate1886 (113/125) (1809/2000) piece1886=true := by decide +kernel
noncomputable def cell1886 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1886 accepted1886 (113/125) (1809/2000) piece1886
    intervalAccepted1886 (fun t => piece_le_psi ⟨1530,by decide +kernel⟩ t)
def piece1887 : AffinePiece := pieces[1531]'(by decide +kernel)
theorem intervalAccepted1887 : candidateIntervalCheck candidate1887 (1809/2000) (181/200) piece1887=true := by decide +kernel
noncomputable def cell1887 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1887 accepted1887 (1809/2000) (181/200) piece1887
    intervalAccepted1887 (fun t => piece_le_psi ⟨1531,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1872, cell1873, cell1874, cell1875, cell1876, cell1877, cell1878, cell1879, cell1880, cell1881, cell1882, cell1883, cell1884, cell1885, cell1886, cell1887]
theorem chainAccepted : spinCellChainCheck (897/1000) (181/200) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (897/1000) (181/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0117
