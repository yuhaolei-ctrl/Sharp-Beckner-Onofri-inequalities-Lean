import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0121
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0121
open CandidateBatch0121 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1936 : AffinePiece := pieces[1580]'(by decide +kernel)
theorem intervalAccepted1936 : candidateIntervalCheck candidate1936 (929/1000) (1859/2000) piece1936=true := by decide +kernel
noncomputable def cell1936 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1936 accepted1936 (929/1000) (1859/2000) piece1936
    intervalAccepted1936 (fun t => piece_le_psi ⟨1580,by decide +kernel⟩ t)
def piece1937 : AffinePiece := pieces[1581]'(by decide +kernel)
theorem intervalAccepted1937 : candidateIntervalCheck candidate1937 (1859/2000) (93/100) piece1937=true := by decide +kernel
noncomputable def cell1937 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1937 accepted1937 (1859/2000) (93/100) piece1937
    intervalAccepted1937 (fun t => piece_le_psi ⟨1581,by decide +kernel⟩ t)
def piece1938 : AffinePiece := pieces[1582]'(by decide +kernel)
theorem intervalAccepted1938 : candidateIntervalCheck candidate1938 (93/100) (1861/2000) piece1938=true := by decide +kernel
noncomputable def cell1938 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1938 accepted1938 (93/100) (1861/2000) piece1938
    intervalAccepted1938 (fun t => piece_le_psi ⟨1582,by decide +kernel⟩ t)
def piece1939 : AffinePiece := pieces[1583]'(by decide +kernel)
theorem intervalAccepted1939 : candidateIntervalCheck candidate1939 (1861/2000) (931/1000) piece1939=true := by decide +kernel
noncomputable def cell1939 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1939 accepted1939 (1861/2000) (931/1000) piece1939
    intervalAccepted1939 (fun t => piece_le_psi ⟨1583,by decide +kernel⟩ t)
def piece1940 : AffinePiece := pieces[1584]'(by decide +kernel)
theorem intervalAccepted1940 : candidateIntervalCheck candidate1940 (931/1000) (1863/2000) piece1940=true := by decide +kernel
noncomputable def cell1940 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1940 accepted1940 (931/1000) (1863/2000) piece1940
    intervalAccepted1940 (fun t => piece_le_psi ⟨1584,by decide +kernel⟩ t)
def piece1941 : AffinePiece := pieces[1585]'(by decide +kernel)
theorem intervalAccepted1941 : candidateIntervalCheck candidate1941 (1863/2000) (233/250) piece1941=true := by decide +kernel
noncomputable def cell1941 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1941 accepted1941 (1863/2000) (233/250) piece1941
    intervalAccepted1941 (fun t => piece_le_psi ⟨1585,by decide +kernel⟩ t)
def piece1942 : AffinePiece := pieces[1586]'(by decide +kernel)
theorem intervalAccepted1942 : candidateIntervalCheck candidate1942 (233/250) (373/400) piece1942=true := by decide +kernel
noncomputable def cell1942 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1942 accepted1942 (233/250) (373/400) piece1942
    intervalAccepted1942 (fun t => piece_le_psi ⟨1586,by decide +kernel⟩ t)
def piece1943 : AffinePiece := pieces[1587]'(by decide +kernel)
theorem intervalAccepted1943 : candidateIntervalCheck candidate1943 (373/400) (933/1000) piece1943=true := by decide +kernel
noncomputable def cell1943 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1943 accepted1943 (373/400) (933/1000) piece1943
    intervalAccepted1943 (fun t => piece_le_psi ⟨1587,by decide +kernel⟩ t)
def piece1944 : AffinePiece := pieces[1588]'(by decide +kernel)
theorem intervalAccepted1944 : candidateIntervalCheck candidate1944 (933/1000) (1867/2000) piece1944=true := by decide +kernel
noncomputable def cell1944 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1944 accepted1944 (933/1000) (1867/2000) piece1944
    intervalAccepted1944 (fun t => piece_le_psi ⟨1588,by decide +kernel⟩ t)
def piece1945 : AffinePiece := pieces[1589]'(by decide +kernel)
theorem intervalAccepted1945 : candidateIntervalCheck candidate1945 (1867/2000) (467/500) piece1945=true := by decide +kernel
noncomputable def cell1945 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1945 accepted1945 (1867/2000) (467/500) piece1945
    intervalAccepted1945 (fun t => piece_le_psi ⟨1589,by decide +kernel⟩ t)
def piece1946 : AffinePiece := pieces[1590]'(by decide +kernel)
theorem intervalAccepted1946 : candidateIntervalCheck candidate1946 (467/500) (1869/2000) piece1946=true := by decide +kernel
noncomputable def cell1946 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1946 accepted1946 (467/500) (1869/2000) piece1946
    intervalAccepted1946 (fun t => piece_le_psi ⟨1590,by decide +kernel⟩ t)
def piece1947 : AffinePiece := pieces[1591]'(by decide +kernel)
theorem intervalAccepted1947 : candidateIntervalCheck candidate1947 (1869/2000) (187/200) piece1947=true := by decide +kernel
noncomputable def cell1947 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1947 accepted1947 (1869/2000) (187/200) piece1947
    intervalAccepted1947 (fun t => piece_le_psi ⟨1591,by decide +kernel⟩ t)
def piece1948 : AffinePiece := pieces[1592]'(by decide +kernel)
theorem intervalAccepted1948 : candidateIntervalCheck candidate1948 (187/200) (1871/2000) piece1948=true := by decide +kernel
noncomputable def cell1948 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1948 accepted1948 (187/200) (1871/2000) piece1948
    intervalAccepted1948 (fun t => piece_le_psi ⟨1592,by decide +kernel⟩ t)
def piece1949 : AffinePiece := pieces[1593]'(by decide +kernel)
theorem intervalAccepted1949 : candidateIntervalCheck candidate1949 (1871/2000) (117/125) piece1949=true := by decide +kernel
noncomputable def cell1949 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1949 accepted1949 (1871/2000) (117/125) piece1949
    intervalAccepted1949 (fun t => piece_le_psi ⟨1593,by decide +kernel⟩ t)
def piece1950 : AffinePiece := pieces[1594]'(by decide +kernel)
theorem intervalAccepted1950 : candidateIntervalCheck candidate1950 (117/125) (1873/2000) piece1950=true := by decide +kernel
noncomputable def cell1950 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1950 accepted1950 (117/125) (1873/2000) piece1950
    intervalAccepted1950 (fun t => piece_le_psi ⟨1594,by decide +kernel⟩ t)
def piece1951 : AffinePiece := pieces[1595]'(by decide +kernel)
theorem intervalAccepted1951 : candidateIntervalCheck candidate1951 (1873/2000) (937/1000) piece1951=true := by decide +kernel
noncomputable def cell1951 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1951 accepted1951 (1873/2000) (937/1000) piece1951
    intervalAccepted1951 (fun t => piece_le_psi ⟨1595,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1936, cell1937, cell1938, cell1939, cell1940, cell1941, cell1942, cell1943, cell1944, cell1945, cell1946, cell1947, cell1948, cell1949, cell1950, cell1951]
theorem chainAccepted : spinCellChainCheck (929/1000) (937/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (929/1000) (937/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0121
