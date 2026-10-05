module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0118

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0118
open CandidateBatch0118 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1888 : AffinePiece := pieces[1532]'(by decide +kernel)
theorem intervalAccepted1888 : candidateIntervalCheck candidate1888 (181/200) (1811/2000) piece1888=true := by decide +kernel
noncomputable def cell1888 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1888 accepted1888 (181/200) (1811/2000) piece1888
    intervalAccepted1888 (fun t => piece_le_psi ⟨1532,by decide +kernel⟩ t)
def piece1889 : AffinePiece := pieces[1533]'(by decide +kernel)
theorem intervalAccepted1889 : candidateIntervalCheck candidate1889 (1811/2000) (453/500) piece1889=true := by decide +kernel
noncomputable def cell1889 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1889 accepted1889 (1811/2000) (453/500) piece1889
    intervalAccepted1889 (fun t => piece_le_psi ⟨1533,by decide +kernel⟩ t)
def piece1890 : AffinePiece := pieces[1534]'(by decide +kernel)
theorem intervalAccepted1890 : candidateIntervalCheck candidate1890 (453/500) (1813/2000) piece1890=true := by decide +kernel
noncomputable def cell1890 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1890 accepted1890 (453/500) (1813/2000) piece1890
    intervalAccepted1890 (fun t => piece_le_psi ⟨1534,by decide +kernel⟩ t)
def piece1891 : AffinePiece := pieces[1535]'(by decide +kernel)
theorem intervalAccepted1891 : candidateIntervalCheck candidate1891 (1813/2000) (907/1000) piece1891=true := by decide +kernel
noncomputable def cell1891 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1891 accepted1891 (1813/2000) (907/1000) piece1891
    intervalAccepted1891 (fun t => piece_le_psi ⟨1535,by decide +kernel⟩ t)
def piece1892 : AffinePiece := pieces[1536]'(by decide +kernel)
theorem intervalAccepted1892 : candidateIntervalCheck candidate1892 (907/1000) (363/400) piece1892=true := by decide +kernel
noncomputable def cell1892 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1892 accepted1892 (907/1000) (363/400) piece1892
    intervalAccepted1892 (fun t => piece_le_psi ⟨1536,by decide +kernel⟩ t)
def piece1893 : AffinePiece := pieces[1537]'(by decide +kernel)
theorem intervalAccepted1893 : candidateIntervalCheck candidate1893 (363/400) (227/250) piece1893=true := by decide +kernel
noncomputable def cell1893 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1893 accepted1893 (363/400) (227/250) piece1893
    intervalAccepted1893 (fun t => piece_le_psi ⟨1537,by decide +kernel⟩ t)
def piece1894 : AffinePiece := pieces[1538]'(by decide +kernel)
theorem intervalAccepted1894 : candidateIntervalCheck candidate1894 (227/250) (1817/2000) piece1894=true := by decide +kernel
noncomputable def cell1894 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1894 accepted1894 (227/250) (1817/2000) piece1894
    intervalAccepted1894 (fun t => piece_le_psi ⟨1538,by decide +kernel⟩ t)
def piece1895 : AffinePiece := pieces[1539]'(by decide +kernel)
theorem intervalAccepted1895 : candidateIntervalCheck candidate1895 (1817/2000) (909/1000) piece1895=true := by decide +kernel
noncomputable def cell1895 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1895 accepted1895 (1817/2000) (909/1000) piece1895
    intervalAccepted1895 (fun t => piece_le_psi ⟨1539,by decide +kernel⟩ t)
def piece1896 : AffinePiece := pieces[1540]'(by decide +kernel)
theorem intervalAccepted1896 : candidateIntervalCheck candidate1896 (909/1000) (1819/2000) piece1896=true := by decide +kernel
noncomputable def cell1896 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1896 accepted1896 (909/1000) (1819/2000) piece1896
    intervalAccepted1896 (fun t => piece_le_psi ⟨1540,by decide +kernel⟩ t)
def piece1897 : AffinePiece := pieces[1541]'(by decide +kernel)
theorem intervalAccepted1897 : candidateIntervalCheck candidate1897 (1819/2000) (91/100) piece1897=true := by decide +kernel
noncomputable def cell1897 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1897 accepted1897 (1819/2000) (91/100) piece1897
    intervalAccepted1897 (fun t => piece_le_psi ⟨1541,by decide +kernel⟩ t)
def piece1898 : AffinePiece := pieces[1542]'(by decide +kernel)
theorem intervalAccepted1898 : candidateIntervalCheck candidate1898 (91/100) (1821/2000) piece1898=true := by decide +kernel
noncomputable def cell1898 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1898 accepted1898 (91/100) (1821/2000) piece1898
    intervalAccepted1898 (fun t => piece_le_psi ⟨1542,by decide +kernel⟩ t)
def piece1899 : AffinePiece := pieces[1543]'(by decide +kernel)
theorem intervalAccepted1899 : candidateIntervalCheck candidate1899 (1821/2000) (911/1000) piece1899=true := by decide +kernel
noncomputable def cell1899 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1899 accepted1899 (1821/2000) (911/1000) piece1899
    intervalAccepted1899 (fun t => piece_le_psi ⟨1543,by decide +kernel⟩ t)
def piece1900 : AffinePiece := pieces[1544]'(by decide +kernel)
theorem intervalAccepted1900 : candidateIntervalCheck candidate1900 (911/1000) (1823/2000) piece1900=true := by decide +kernel
noncomputable def cell1900 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1900 accepted1900 (911/1000) (1823/2000) piece1900
    intervalAccepted1900 (fun t => piece_le_psi ⟨1544,by decide +kernel⟩ t)
def piece1901 : AffinePiece := pieces[1545]'(by decide +kernel)
theorem intervalAccepted1901 : candidateIntervalCheck candidate1901 (1823/2000) (114/125) piece1901=true := by decide +kernel
noncomputable def cell1901 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1901 accepted1901 (1823/2000) (114/125) piece1901
    intervalAccepted1901 (fun t => piece_le_psi ⟨1545,by decide +kernel⟩ t)
def piece1902 : AffinePiece := pieces[1546]'(by decide +kernel)
theorem intervalAccepted1902 : candidateIntervalCheck candidate1902 (114/125) (73/80) piece1902=true := by decide +kernel
noncomputable def cell1902 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1902 accepted1902 (114/125) (73/80) piece1902
    intervalAccepted1902 (fun t => piece_le_psi ⟨1546,by decide +kernel⟩ t)
def piece1903 : AffinePiece := pieces[1547]'(by decide +kernel)
theorem intervalAccepted1903 : candidateIntervalCheck candidate1903 (73/80) (913/1000) piece1903=true := by decide +kernel
noncomputable def cell1903 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1903 accepted1903 (73/80) (913/1000) piece1903
    intervalAccepted1903 (fun t => piece_le_psi ⟨1547,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1888, cell1889, cell1890, cell1891, cell1892, cell1893, cell1894, cell1895, cell1896, cell1897, cell1898, cell1899, cell1900, cell1901, cell1902, cell1903]
theorem chainAccepted : spinCellChainCheck (181/200) (913/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (181/200) (913/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0118
