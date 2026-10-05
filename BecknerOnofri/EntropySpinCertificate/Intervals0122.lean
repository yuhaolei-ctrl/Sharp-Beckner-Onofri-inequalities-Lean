import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0122
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0122
open CandidateBatch0122 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1952 : AffinePiece := pieces[1596]'(by decide +kernel)
theorem intervalAccepted1952 : candidateIntervalCheck candidate1952 (937/1000) (15/16) piece1952=true := by decide +kernel
noncomputable def cell1952 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1952 accepted1952 (937/1000) (15/16) piece1952
    intervalAccepted1952 (fun t => piece_le_psi ⟨1596,by decide +kernel⟩ t)
def piece1953 : AffinePiece := pieces[1597]'(by decide +kernel)
theorem intervalAccepted1953 : candidateIntervalCheck candidate1953 (15/16) (469/500) piece1953=true := by decide +kernel
noncomputable def cell1953 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1953 accepted1953 (15/16) (469/500) piece1953
    intervalAccepted1953 (fun t => piece_le_psi ⟨1597,by decide +kernel⟩ t)
def piece1954 : AffinePiece := pieces[1598]'(by decide +kernel)
theorem intervalAccepted1954 : candidateIntervalCheck candidate1954 (469/500) (1877/2000) piece1954=true := by decide +kernel
noncomputable def cell1954 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1954 accepted1954 (469/500) (1877/2000) piece1954
    intervalAccepted1954 (fun t => piece_le_psi ⟨1598,by decide +kernel⟩ t)
def piece1955 : AffinePiece := pieces[1599]'(by decide +kernel)
theorem intervalAccepted1955 : candidateIntervalCheck candidate1955 (1877/2000) (939/1000) piece1955=true := by decide +kernel
noncomputable def cell1955 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1955 accepted1955 (1877/2000) (939/1000) piece1955
    intervalAccepted1955 (fun t => piece_le_psi ⟨1599,by decide +kernel⟩ t)
def piece1956 : AffinePiece := pieces[1600]'(by decide +kernel)
theorem intervalAccepted1956 : candidateIntervalCheck candidate1956 (939/1000) (1879/2000) piece1956=true := by decide +kernel
noncomputable def cell1956 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1956 accepted1956 (939/1000) (1879/2000) piece1956
    intervalAccepted1956 (fun t => piece_le_psi ⟨1600,by decide +kernel⟩ t)
def piece1957 : AffinePiece := pieces[1601]'(by decide +kernel)
theorem intervalAccepted1957 : candidateIntervalCheck candidate1957 (1879/2000) (47/50) piece1957=true := by decide +kernel
noncomputable def cell1957 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1957 accepted1957 (1879/2000) (47/50) piece1957
    intervalAccepted1957 (fun t => piece_le_psi ⟨1601,by decide +kernel⟩ t)
def piece1958 : AffinePiece := pieces[1602]'(by decide +kernel)
theorem intervalAccepted1958 : candidateIntervalCheck candidate1958 (47/50) (1881/2000) piece1958=true := by decide +kernel
noncomputable def cell1958 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1958 accepted1958 (47/50) (1881/2000) piece1958
    intervalAccepted1958 (fun t => piece_le_psi ⟨1602,by decide +kernel⟩ t)
def piece1959 : AffinePiece := pieces[1603]'(by decide +kernel)
theorem intervalAccepted1959 : candidateIntervalCheck candidate1959 (1881/2000) (941/1000) piece1959=true := by decide +kernel
noncomputable def cell1959 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1959 accepted1959 (1881/2000) (941/1000) piece1959
    intervalAccepted1959 (fun t => piece_le_psi ⟨1603,by decide +kernel⟩ t)
def piece1960 : AffinePiece := pieces[1604]'(by decide +kernel)
theorem intervalAccepted1960 : candidateIntervalCheck candidate1960 (941/1000) (1883/2000) piece1960=true := by decide +kernel
noncomputable def cell1960 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1960 accepted1960 (941/1000) (1883/2000) piece1960
    intervalAccepted1960 (fun t => piece_le_psi ⟨1604,by decide +kernel⟩ t)
def piece1961 : AffinePiece := pieces[1605]'(by decide +kernel)
theorem intervalAccepted1961 : candidateIntervalCheck candidate1961 (1883/2000) (471/500) piece1961=true := by decide +kernel
noncomputable def cell1961 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1961 accepted1961 (1883/2000) (471/500) piece1961
    intervalAccepted1961 (fun t => piece_le_psi ⟨1605,by decide +kernel⟩ t)
def piece1962 : AffinePiece := pieces[1606]'(by decide +kernel)
theorem intervalAccepted1962 : candidateIntervalCheck candidate1962 (471/500) (377/400) piece1962=true := by decide +kernel
noncomputable def cell1962 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1962 accepted1962 (471/500) (377/400) piece1962
    intervalAccepted1962 (fun t => piece_le_psi ⟨1606,by decide +kernel⟩ t)
def piece1963 : AffinePiece := pieces[1607]'(by decide +kernel)
theorem intervalAccepted1963 : candidateIntervalCheck candidate1963 (377/400) (943/1000) piece1963=true := by decide +kernel
noncomputable def cell1963 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1963 accepted1963 (377/400) (943/1000) piece1963
    intervalAccepted1963 (fun t => piece_le_psi ⟨1607,by decide +kernel⟩ t)
def piece1964 : AffinePiece := pieces[1608]'(by decide +kernel)
theorem intervalAccepted1964 : candidateIntervalCheck candidate1964 (943/1000) (1887/2000) piece1964=true := by decide +kernel
noncomputable def cell1964 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1964 accepted1964 (943/1000) (1887/2000) piece1964
    intervalAccepted1964 (fun t => piece_le_psi ⟨1608,by decide +kernel⟩ t)
def piece1965 : AffinePiece := pieces[1609]'(by decide +kernel)
theorem intervalAccepted1965 : candidateIntervalCheck candidate1965 (1887/2000) (118/125) piece1965=true := by decide +kernel
noncomputable def cell1965 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1965 accepted1965 (1887/2000) (118/125) piece1965
    intervalAccepted1965 (fun t => piece_le_psi ⟨1609,by decide +kernel⟩ t)
def piece1966 : AffinePiece := pieces[1610]'(by decide +kernel)
theorem intervalAccepted1966 : candidateIntervalCheck candidate1966 (118/125) (1889/2000) piece1966=true := by decide +kernel
noncomputable def cell1966 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1966 accepted1966 (118/125) (1889/2000) piece1966
    intervalAccepted1966 (fun t => piece_le_psi ⟨1610,by decide +kernel⟩ t)
def piece1967 : AffinePiece := pieces[1611]'(by decide +kernel)
theorem intervalAccepted1967 : candidateIntervalCheck candidate1967 (1889/2000) (189/200) piece1967=true := by decide +kernel
noncomputable def cell1967 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1967 accepted1967 (1889/2000) (189/200) piece1967
    intervalAccepted1967 (fun t => piece_le_psi ⟨1611,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1952, cell1953, cell1954, cell1955, cell1956, cell1957, cell1958, cell1959, cell1960, cell1961, cell1962, cell1963, cell1964, cell1965, cell1966, cell1967]
theorem chainAccepted : spinCellChainCheck (937/1000) (189/200) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (937/1000) (189/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0122
