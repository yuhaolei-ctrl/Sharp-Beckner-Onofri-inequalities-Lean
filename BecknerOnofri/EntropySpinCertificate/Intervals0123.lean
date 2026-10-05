import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0123
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0123
open CandidateBatch0123 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1968 : AffinePiece := pieces[1612]'(by decide +kernel)
theorem intervalAccepted1968 : candidateIntervalCheck candidate1968 (189/200) (1891/2000) piece1968=true := by decide +kernel
noncomputable def cell1968 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1968 accepted1968 (189/200) (1891/2000) piece1968
    intervalAccepted1968 (fun t => piece_le_psi ⟨1612,by decide +kernel⟩ t)
def piece1969 : AffinePiece := pieces[1613]'(by decide +kernel)
theorem intervalAccepted1969 : candidateIntervalCheck candidate1969 (1891/2000) (473/500) piece1969=true := by decide +kernel
noncomputable def cell1969 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1969 accepted1969 (1891/2000) (473/500) piece1969
    intervalAccepted1969 (fun t => piece_le_psi ⟨1613,by decide +kernel⟩ t)
def piece1970 : AffinePiece := pieces[1614]'(by decide +kernel)
theorem intervalAccepted1970 : candidateIntervalCheck candidate1970 (473/500) (1893/2000) piece1970=true := by decide +kernel
noncomputable def cell1970 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1970 accepted1970 (473/500) (1893/2000) piece1970
    intervalAccepted1970 (fun t => piece_le_psi ⟨1614,by decide +kernel⟩ t)
def piece1971 : AffinePiece := pieces[1615]'(by decide +kernel)
theorem intervalAccepted1971 : candidateIntervalCheck candidate1971 (1893/2000) (947/1000) piece1971=true := by decide +kernel
noncomputable def cell1971 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1971 accepted1971 (1893/2000) (947/1000) piece1971
    intervalAccepted1971 (fun t => piece_le_psi ⟨1615,by decide +kernel⟩ t)
def piece1972 : AffinePiece := pieces[1616]'(by decide +kernel)
theorem intervalAccepted1972 : candidateIntervalCheck candidate1972 (947/1000) (379/400) piece1972=true := by decide +kernel
noncomputable def cell1972 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1972 accepted1972 (947/1000) (379/400) piece1972
    intervalAccepted1972 (fun t => piece_le_psi ⟨1616,by decide +kernel⟩ t)
def piece1973 : AffinePiece := pieces[1617]'(by decide +kernel)
theorem intervalAccepted1973 : candidateIntervalCheck candidate1973 (379/400) (237/250) piece1973=true := by decide +kernel
noncomputable def cell1973 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1973 accepted1973 (379/400) (237/250) piece1973
    intervalAccepted1973 (fun t => piece_le_psi ⟨1617,by decide +kernel⟩ t)
def piece1974 : AffinePiece := pieces[1618]'(by decide +kernel)
theorem intervalAccepted1974 : candidateIntervalCheck candidate1974 (237/250) (1897/2000) piece1974=true := by decide +kernel
noncomputable def cell1974 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1974 accepted1974 (237/250) (1897/2000) piece1974
    intervalAccepted1974 (fun t => piece_le_psi ⟨1618,by decide +kernel⟩ t)
def piece1975 : AffinePiece := pieces[1619]'(by decide +kernel)
theorem intervalAccepted1975 : candidateIntervalCheck candidate1975 (1897/2000) (949/1000) piece1975=true := by decide +kernel
noncomputable def cell1975 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1975 accepted1975 (1897/2000) (949/1000) piece1975
    intervalAccepted1975 (fun t => piece_le_psi ⟨1619,by decide +kernel⟩ t)
def piece1976 : AffinePiece := pieces[1620]'(by decide +kernel)
theorem intervalAccepted1976 : candidateIntervalCheck candidate1976 (949/1000) (1899/2000) piece1976=true := by decide +kernel
noncomputable def cell1976 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1976 accepted1976 (949/1000) (1899/2000) piece1976
    intervalAccepted1976 (fun t => piece_le_psi ⟨1620,by decide +kernel⟩ t)
def piece1977 : AffinePiece := pieces[1621]'(by decide +kernel)
theorem intervalAccepted1977 : candidateIntervalCheck candidate1977 (1899/2000) (19/20) piece1977=true := by decide +kernel
noncomputable def cell1977 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1977 accepted1977 (1899/2000) (19/20) piece1977
    intervalAccepted1977 (fun t => piece_le_psi ⟨1621,by decide +kernel⟩ t)
def piece1978 : AffinePiece := pieces[1621]'(by decide +kernel)
theorem intervalAccepted1978 : candidateIntervalCheck candidate1978 (19/20) (197/200) piece1978=true := by decide +kernel
noncomputable def cell1978 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1978 accepted1978 (19/20) (197/200) piece1978
    intervalAccepted1978 (fun t => piece_le_psi ⟨1621,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1968, cell1969, cell1970, cell1971, cell1972, cell1973, cell1974, cell1975, cell1976, cell1977, cell1978]
theorem chainAccepted : spinCellChainCheck (189/200) (197/200) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (189/200) (197/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0123
