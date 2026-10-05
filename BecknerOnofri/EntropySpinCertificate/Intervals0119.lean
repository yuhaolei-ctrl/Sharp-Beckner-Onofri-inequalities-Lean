import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0119
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0119
open CandidateBatch0119 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1904 : AffinePiece := pieces[1548]'(by decide +kernel)
theorem intervalAccepted1904 : candidateIntervalCheck candidate1904 (913/1000) (1827/2000) piece1904=true := by decide +kernel
noncomputable def cell1904 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1904 accepted1904 (913/1000) (1827/2000) piece1904
    intervalAccepted1904 (fun t => piece_le_psi ⟨1548,by decide +kernel⟩ t)
def piece1905 : AffinePiece := pieces[1549]'(by decide +kernel)
theorem intervalAccepted1905 : candidateIntervalCheck candidate1905 (1827/2000) (457/500) piece1905=true := by decide +kernel
noncomputable def cell1905 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1905 accepted1905 (1827/2000) (457/500) piece1905
    intervalAccepted1905 (fun t => piece_le_psi ⟨1549,by decide +kernel⟩ t)
def piece1906 : AffinePiece := pieces[1550]'(by decide +kernel)
theorem intervalAccepted1906 : candidateIntervalCheck candidate1906 (457/500) (1829/2000) piece1906=true := by decide +kernel
noncomputable def cell1906 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1906 accepted1906 (457/500) (1829/2000) piece1906
    intervalAccepted1906 (fun t => piece_le_psi ⟨1550,by decide +kernel⟩ t)
def piece1907 : AffinePiece := pieces[1551]'(by decide +kernel)
theorem intervalAccepted1907 : candidateIntervalCheck candidate1907 (1829/2000) (183/200) piece1907=true := by decide +kernel
noncomputable def cell1907 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1907 accepted1907 (1829/2000) (183/200) piece1907
    intervalAccepted1907 (fun t => piece_le_psi ⟨1551,by decide +kernel⟩ t)
def piece1908 : AffinePiece := pieces[1552]'(by decide +kernel)
theorem intervalAccepted1908 : candidateIntervalCheck candidate1908 (183/200) (1831/2000) piece1908=true := by decide +kernel
noncomputable def cell1908 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1908 accepted1908 (183/200) (1831/2000) piece1908
    intervalAccepted1908 (fun t => piece_le_psi ⟨1552,by decide +kernel⟩ t)
def piece1909 : AffinePiece := pieces[1553]'(by decide +kernel)
theorem intervalAccepted1909 : candidateIntervalCheck candidate1909 (1831/2000) (229/250) piece1909=true := by decide +kernel
noncomputable def cell1909 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1909 accepted1909 (1831/2000) (229/250) piece1909
    intervalAccepted1909 (fun t => piece_le_psi ⟨1553,by decide +kernel⟩ t)
def piece1910 : AffinePiece := pieces[1554]'(by decide +kernel)
theorem intervalAccepted1910 : candidateIntervalCheck candidate1910 (229/250) (1833/2000) piece1910=true := by decide +kernel
noncomputable def cell1910 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1910 accepted1910 (229/250) (1833/2000) piece1910
    intervalAccepted1910 (fun t => piece_le_psi ⟨1554,by decide +kernel⟩ t)
def piece1911 : AffinePiece := pieces[1555]'(by decide +kernel)
theorem intervalAccepted1911 : candidateIntervalCheck candidate1911 (1833/2000) (917/1000) piece1911=true := by decide +kernel
noncomputable def cell1911 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1911 accepted1911 (1833/2000) (917/1000) piece1911
    intervalAccepted1911 (fun t => piece_le_psi ⟨1555,by decide +kernel⟩ t)
def piece1912 : AffinePiece := pieces[1556]'(by decide +kernel)
theorem intervalAccepted1912 : candidateIntervalCheck candidate1912 (917/1000) (367/400) piece1912=true := by decide +kernel
noncomputable def cell1912 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1912 accepted1912 (917/1000) (367/400) piece1912
    intervalAccepted1912 (fun t => piece_le_psi ⟨1556,by decide +kernel⟩ t)
def piece1913 : AffinePiece := pieces[1557]'(by decide +kernel)
theorem intervalAccepted1913 : candidateIntervalCheck candidate1913 (367/400) (459/500) piece1913=true := by decide +kernel
noncomputable def cell1913 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1913 accepted1913 (367/400) (459/500) piece1913
    intervalAccepted1913 (fun t => piece_le_psi ⟨1557,by decide +kernel⟩ t)
def piece1914 : AffinePiece := pieces[1558]'(by decide +kernel)
theorem intervalAccepted1914 : candidateIntervalCheck candidate1914 (459/500) (1837/2000) piece1914=true := by decide +kernel
noncomputable def cell1914 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1914 accepted1914 (459/500) (1837/2000) piece1914
    intervalAccepted1914 (fun t => piece_le_psi ⟨1558,by decide +kernel⟩ t)
def piece1915 : AffinePiece := pieces[1559]'(by decide +kernel)
theorem intervalAccepted1915 : candidateIntervalCheck candidate1915 (1837/2000) (919/1000) piece1915=true := by decide +kernel
noncomputable def cell1915 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1915 accepted1915 (1837/2000) (919/1000) piece1915
    intervalAccepted1915 (fun t => piece_le_psi ⟨1559,by decide +kernel⟩ t)
def piece1916 : AffinePiece := pieces[1560]'(by decide +kernel)
theorem intervalAccepted1916 : candidateIntervalCheck candidate1916 (919/1000) (1839/2000) piece1916=true := by decide +kernel
noncomputable def cell1916 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1916 accepted1916 (919/1000) (1839/2000) piece1916
    intervalAccepted1916 (fun t => piece_le_psi ⟨1560,by decide +kernel⟩ t)
def piece1917 : AffinePiece := pieces[1561]'(by decide +kernel)
theorem intervalAccepted1917 : candidateIntervalCheck candidate1917 (1839/2000) (23/25) piece1917=true := by decide +kernel
noncomputable def cell1917 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1917 accepted1917 (1839/2000) (23/25) piece1917
    intervalAccepted1917 (fun t => piece_le_psi ⟨1561,by decide +kernel⟩ t)
def piece1918 : AffinePiece := pieces[1562]'(by decide +kernel)
theorem intervalAccepted1918 : candidateIntervalCheck candidate1918 (23/25) (1841/2000) piece1918=true := by decide +kernel
noncomputable def cell1918 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1918 accepted1918 (23/25) (1841/2000) piece1918
    intervalAccepted1918 (fun t => piece_le_psi ⟨1562,by decide +kernel⟩ t)
def piece1919 : AffinePiece := pieces[1563]'(by decide +kernel)
theorem intervalAccepted1919 : candidateIntervalCheck candidate1919 (1841/2000) (921/1000) piece1919=true := by decide +kernel
noncomputable def cell1919 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1919 accepted1919 (1841/2000) (921/1000) piece1919
    intervalAccepted1919 (fun t => piece_le_psi ⟨1563,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1904, cell1905, cell1906, cell1907, cell1908, cell1909, cell1910, cell1911, cell1912, cell1913, cell1914, cell1915, cell1916, cell1917, cell1918, cell1919]
theorem chainAccepted : spinCellChainCheck (913/1000) (921/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (913/1000) (921/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0119
