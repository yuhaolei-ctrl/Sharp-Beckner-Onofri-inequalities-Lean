import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0120
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0120
open CandidateBatch0120 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1920 : AffinePiece := pieces[1564]'(by decide +kernel)
theorem intervalAccepted1920 : candidateIntervalCheck candidate1920 (921/1000) (1843/2000) piece1920=true := by decide +kernel
noncomputable def cell1920 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1920 accepted1920 (921/1000) (1843/2000) piece1920
    intervalAccepted1920 (fun t => piece_le_psi ⟨1564,by decide +kernel⟩ t)
def piece1921 : AffinePiece := pieces[1565]'(by decide +kernel)
theorem intervalAccepted1921 : candidateIntervalCheck candidate1921 (1843/2000) (461/500) piece1921=true := by decide +kernel
noncomputable def cell1921 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1921 accepted1921 (1843/2000) (461/500) piece1921
    intervalAccepted1921 (fun t => piece_le_psi ⟨1565,by decide +kernel⟩ t)
def piece1922 : AffinePiece := pieces[1566]'(by decide +kernel)
theorem intervalAccepted1922 : candidateIntervalCheck candidate1922 (461/500) (369/400) piece1922=true := by decide +kernel
noncomputable def cell1922 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1922 accepted1922 (461/500) (369/400) piece1922
    intervalAccepted1922 (fun t => piece_le_psi ⟨1566,by decide +kernel⟩ t)
def piece1923 : AffinePiece := pieces[1567]'(by decide +kernel)
theorem intervalAccepted1923 : candidateIntervalCheck candidate1923 (369/400) (923/1000) piece1923=true := by decide +kernel
noncomputable def cell1923 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1923 accepted1923 (369/400) (923/1000) piece1923
    intervalAccepted1923 (fun t => piece_le_psi ⟨1567,by decide +kernel⟩ t)
def piece1924 : AffinePiece := pieces[1568]'(by decide +kernel)
theorem intervalAccepted1924 : candidateIntervalCheck candidate1924 (923/1000) (1847/2000) piece1924=true := by decide +kernel
noncomputable def cell1924 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1924 accepted1924 (923/1000) (1847/2000) piece1924
    intervalAccepted1924 (fun t => piece_le_psi ⟨1568,by decide +kernel⟩ t)
def piece1925 : AffinePiece := pieces[1569]'(by decide +kernel)
theorem intervalAccepted1925 : candidateIntervalCheck candidate1925 (1847/2000) (231/250) piece1925=true := by decide +kernel
noncomputable def cell1925 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1925 accepted1925 (1847/2000) (231/250) piece1925
    intervalAccepted1925 (fun t => piece_le_psi ⟨1569,by decide +kernel⟩ t)
def piece1926 : AffinePiece := pieces[1570]'(by decide +kernel)
theorem intervalAccepted1926 : candidateIntervalCheck candidate1926 (231/250) (1849/2000) piece1926=true := by decide +kernel
noncomputable def cell1926 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1926 accepted1926 (231/250) (1849/2000) piece1926
    intervalAccepted1926 (fun t => piece_le_psi ⟨1570,by decide +kernel⟩ t)
def piece1927 : AffinePiece := pieces[1571]'(by decide +kernel)
theorem intervalAccepted1927 : candidateIntervalCheck candidate1927 (1849/2000) (37/40) piece1927=true := by decide +kernel
noncomputable def cell1927 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1927 accepted1927 (1849/2000) (37/40) piece1927
    intervalAccepted1927 (fun t => piece_le_psi ⟨1571,by decide +kernel⟩ t)
def piece1928 : AffinePiece := pieces[1572]'(by decide +kernel)
theorem intervalAccepted1928 : candidateIntervalCheck candidate1928 (37/40) (1851/2000) piece1928=true := by decide +kernel
noncomputable def cell1928 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1928 accepted1928 (37/40) (1851/2000) piece1928
    intervalAccepted1928 (fun t => piece_le_psi ⟨1572,by decide +kernel⟩ t)
def piece1929 : AffinePiece := pieces[1573]'(by decide +kernel)
theorem intervalAccepted1929 : candidateIntervalCheck candidate1929 (1851/2000) (463/500) piece1929=true := by decide +kernel
noncomputable def cell1929 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1929 accepted1929 (1851/2000) (463/500) piece1929
    intervalAccepted1929 (fun t => piece_le_psi ⟨1573,by decide +kernel⟩ t)
def piece1930 : AffinePiece := pieces[1574]'(by decide +kernel)
theorem intervalAccepted1930 : candidateIntervalCheck candidate1930 (463/500) (1853/2000) piece1930=true := by decide +kernel
noncomputable def cell1930 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1930 accepted1930 (463/500) (1853/2000) piece1930
    intervalAccepted1930 (fun t => piece_le_psi ⟨1574,by decide +kernel⟩ t)
def piece1931 : AffinePiece := pieces[1575]'(by decide +kernel)
theorem intervalAccepted1931 : candidateIntervalCheck candidate1931 (1853/2000) (927/1000) piece1931=true := by decide +kernel
noncomputable def cell1931 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1931 accepted1931 (1853/2000) (927/1000) piece1931
    intervalAccepted1931 (fun t => piece_le_psi ⟨1575,by decide +kernel⟩ t)
def piece1932 : AffinePiece := pieces[1576]'(by decide +kernel)
theorem intervalAccepted1932 : candidateIntervalCheck candidate1932 (927/1000) (371/400) piece1932=true := by decide +kernel
noncomputable def cell1932 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1932 accepted1932 (927/1000) (371/400) piece1932
    intervalAccepted1932 (fun t => piece_le_psi ⟨1576,by decide +kernel⟩ t)
def piece1933 : AffinePiece := pieces[1577]'(by decide +kernel)
theorem intervalAccepted1933 : candidateIntervalCheck candidate1933 (371/400) (116/125) piece1933=true := by decide +kernel
noncomputable def cell1933 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1933 accepted1933 (371/400) (116/125) piece1933
    intervalAccepted1933 (fun t => piece_le_psi ⟨1577,by decide +kernel⟩ t)
def piece1934 : AffinePiece := pieces[1578]'(by decide +kernel)
theorem intervalAccepted1934 : candidateIntervalCheck candidate1934 (116/125) (1857/2000) piece1934=true := by decide +kernel
noncomputable def cell1934 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1934 accepted1934 (116/125) (1857/2000) piece1934
    intervalAccepted1934 (fun t => piece_le_psi ⟨1578,by decide +kernel⟩ t)
def piece1935 : AffinePiece := pieces[1579]'(by decide +kernel)
theorem intervalAccepted1935 : candidateIntervalCheck candidate1935 (1857/2000) (929/1000) piece1935=true := by decide +kernel
noncomputable def cell1935 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1935 accepted1935 (1857/2000) (929/1000) piece1935
    intervalAccepted1935 (fun t => piece_le_psi ⟨1579,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1920, cell1921, cell1922, cell1923, cell1924, cell1925, cell1926, cell1927, cell1928, cell1929, cell1930, cell1931, cell1932, cell1933, cell1934, cell1935]
theorem chainAccepted : spinCellChainCheck (921/1000) (929/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (921/1000) (929/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0120
