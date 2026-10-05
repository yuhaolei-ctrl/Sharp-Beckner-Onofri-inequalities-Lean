import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0066
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0066
open CandidateBatch0066 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1056 : AffinePiece := pieces[954]'(by decide +kernel)
theorem intervalAccepted1056 : candidateIntervalCheck candidate1056 (269/500) (539/1000) piece1056=true := by decide +kernel
noncomputable def cell1056 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1056 accepted1056 (269/500) (539/1000) piece1056
    intervalAccepted1056 (fun t => piece_le_psi ⟨954,by decide +kernel⟩ t)
def piece1057 : AffinePiece := pieces[955]'(by decide +kernel)
theorem intervalAccepted1057 : candidateIntervalCheck candidate1057 (539/1000) (27/50) piece1057=true := by decide +kernel
noncomputable def cell1057 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1057 accepted1057 (539/1000) (27/50) piece1057
    intervalAccepted1057 (fun t => piece_le_psi ⟨955,by decide +kernel⟩ t)
def piece1058 : AffinePiece := pieces[956]'(by decide +kernel)
theorem intervalAccepted1058 : candidateIntervalCheck candidate1058 (27/50) (541/1000) piece1058=true := by decide +kernel
noncomputable def cell1058 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1058 accepted1058 (27/50) (541/1000) piece1058
    intervalAccepted1058 (fun t => piece_le_psi ⟨956,by decide +kernel⟩ t)
def piece1059 : AffinePiece := pieces[957]'(by decide +kernel)
theorem intervalAccepted1059 : candidateIntervalCheck candidate1059 (541/1000) (271/500) piece1059=true := by decide +kernel
noncomputable def cell1059 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1059 accepted1059 (541/1000) (271/500) piece1059
    intervalAccepted1059 (fun t => piece_le_psi ⟨957,by decide +kernel⟩ t)
def piece1060 : AffinePiece := pieces[958]'(by decide +kernel)
theorem intervalAccepted1060 : candidateIntervalCheck candidate1060 (271/500) (543/1000) piece1060=true := by decide +kernel
noncomputable def cell1060 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1060 accepted1060 (271/500) (543/1000) piece1060
    intervalAccepted1060 (fun t => piece_le_psi ⟨958,by decide +kernel⟩ t)
def piece1061 : AffinePiece := pieces[959]'(by decide +kernel)
theorem intervalAccepted1061 : candidateIntervalCheck candidate1061 (543/1000) (68/125) piece1061=true := by decide +kernel
noncomputable def cell1061 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1061 accepted1061 (543/1000) (68/125) piece1061
    intervalAccepted1061 (fun t => piece_le_psi ⟨959,by decide +kernel⟩ t)
def piece1062 : AffinePiece := pieces[960]'(by decide +kernel)
theorem intervalAccepted1062 : candidateIntervalCheck candidate1062 (68/125) (109/200) piece1062=true := by decide +kernel
noncomputable def cell1062 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1062 accepted1062 (68/125) (109/200) piece1062
    intervalAccepted1062 (fun t => piece_le_psi ⟨960,by decide +kernel⟩ t)
def piece1063 : AffinePiece := pieces[961]'(by decide +kernel)
theorem intervalAccepted1063 : candidateIntervalCheck candidate1063 (109/200) (273/500) piece1063=true := by decide +kernel
noncomputable def cell1063 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1063 accepted1063 (109/200) (273/500) piece1063
    intervalAccepted1063 (fun t => piece_le_psi ⟨961,by decide +kernel⟩ t)
def piece1064 : AffinePiece := pieces[962]'(by decide +kernel)
theorem intervalAccepted1064 : candidateIntervalCheck candidate1064 (273/500) (547/1000) piece1064=true := by decide +kernel
noncomputable def cell1064 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1064 accepted1064 (273/500) (547/1000) piece1064
    intervalAccepted1064 (fun t => piece_le_psi ⟨962,by decide +kernel⟩ t)
def piece1065 : AffinePiece := pieces[963]'(by decide +kernel)
theorem intervalAccepted1065 : candidateIntervalCheck candidate1065 (547/1000) (137/250) piece1065=true := by decide +kernel
noncomputable def cell1065 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1065 accepted1065 (547/1000) (137/250) piece1065
    intervalAccepted1065 (fun t => piece_le_psi ⟨963,by decide +kernel⟩ t)
def piece1066 : AffinePiece := pieces[964]'(by decide +kernel)
theorem intervalAccepted1066 : candidateIntervalCheck candidate1066 (137/250) (549/1000) piece1066=true := by decide +kernel
noncomputable def cell1066 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1066 accepted1066 (137/250) (549/1000) piece1066
    intervalAccepted1066 (fun t => piece_le_psi ⟨964,by decide +kernel⟩ t)
def piece1067 : AffinePiece := pieces[965]'(by decide +kernel)
theorem intervalAccepted1067 : candidateIntervalCheck candidate1067 (549/1000) (11/20) piece1067=true := by decide +kernel
noncomputable def cell1067 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1067 accepted1067 (549/1000) (11/20) piece1067
    intervalAccepted1067 (fun t => piece_le_psi ⟨965,by decide +kernel⟩ t)
def piece1068 : AffinePiece := pieces[966]'(by decide +kernel)
theorem intervalAccepted1068 : candidateIntervalCheck candidate1068 (11/20) (551/1000) piece1068=true := by decide +kernel
noncomputable def cell1068 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1068 accepted1068 (11/20) (551/1000) piece1068
    intervalAccepted1068 (fun t => piece_le_psi ⟨966,by decide +kernel⟩ t)
def piece1069 : AffinePiece := pieces[967]'(by decide +kernel)
theorem intervalAccepted1069 : candidateIntervalCheck candidate1069 (551/1000) (69/125) piece1069=true := by decide +kernel
noncomputable def cell1069 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1069 accepted1069 (551/1000) (69/125) piece1069
    intervalAccepted1069 (fun t => piece_le_psi ⟨967,by decide +kernel⟩ t)
def piece1070 : AffinePiece := pieces[968]'(by decide +kernel)
theorem intervalAccepted1070 : candidateIntervalCheck candidate1070 (69/125) (553/1000) piece1070=true := by decide +kernel
noncomputable def cell1070 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1070 accepted1070 (69/125) (553/1000) piece1070
    intervalAccepted1070 (fun t => piece_le_psi ⟨968,by decide +kernel⟩ t)
def piece1071 : AffinePiece := pieces[969]'(by decide +kernel)
theorem intervalAccepted1071 : candidateIntervalCheck candidate1071 (553/1000) (277/500) piece1071=true := by decide +kernel
noncomputable def cell1071 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1071 accepted1071 (553/1000) (277/500) piece1071
    intervalAccepted1071 (fun t => piece_le_psi ⟨969,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1056, cell1057, cell1058, cell1059, cell1060, cell1061, cell1062, cell1063, cell1064, cell1065, cell1066, cell1067, cell1068, cell1069, cell1070, cell1071]
theorem chainAccepted : spinCellChainCheck (269/500) (277/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (269/500) (277/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0066
