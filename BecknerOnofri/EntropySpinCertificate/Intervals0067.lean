import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0067
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0067
open CandidateBatch0067 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1072 : AffinePiece := pieces[970]'(by decide +kernel)
theorem intervalAccepted1072 : candidateIntervalCheck candidate1072 (277/500) (111/200) piece1072=true := by decide +kernel
noncomputable def cell1072 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1072 accepted1072 (277/500) (111/200) piece1072
    intervalAccepted1072 (fun t => piece_le_psi ⟨970,by decide +kernel⟩ t)
def piece1073 : AffinePiece := pieces[971]'(by decide +kernel)
theorem intervalAccepted1073 : candidateIntervalCheck candidate1073 (111/200) (139/250) piece1073=true := by decide +kernel
noncomputable def cell1073 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1073 accepted1073 (111/200) (139/250) piece1073
    intervalAccepted1073 (fun t => piece_le_psi ⟨971,by decide +kernel⟩ t)
def piece1074 : AffinePiece := pieces[972]'(by decide +kernel)
theorem intervalAccepted1074 : candidateIntervalCheck candidate1074 (139/250) (557/1000) piece1074=true := by decide +kernel
noncomputable def cell1074 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1074 accepted1074 (139/250) (557/1000) piece1074
    intervalAccepted1074 (fun t => piece_le_psi ⟨972,by decide +kernel⟩ t)
def piece1075 : AffinePiece := pieces[973]'(by decide +kernel)
theorem intervalAccepted1075 : candidateIntervalCheck candidate1075 (557/1000) (279/500) piece1075=true := by decide +kernel
noncomputable def cell1075 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1075 accepted1075 (557/1000) (279/500) piece1075
    intervalAccepted1075 (fun t => piece_le_psi ⟨973,by decide +kernel⟩ t)
def piece1076 : AffinePiece := pieces[974]'(by decide +kernel)
theorem intervalAccepted1076 : candidateIntervalCheck candidate1076 (279/500) (559/1000) piece1076=true := by decide +kernel
noncomputable def cell1076 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1076 accepted1076 (279/500) (559/1000) piece1076
    intervalAccepted1076 (fun t => piece_le_psi ⟨974,by decide +kernel⟩ t)
def piece1077 : AffinePiece := pieces[975]'(by decide +kernel)
theorem intervalAccepted1077 : candidateIntervalCheck candidate1077 (559/1000) (14/25) piece1077=true := by decide +kernel
noncomputable def cell1077 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1077 accepted1077 (559/1000) (14/25) piece1077
    intervalAccepted1077 (fun t => piece_le_psi ⟨975,by decide +kernel⟩ t)
def piece1078 : AffinePiece := pieces[976]'(by decide +kernel)
theorem intervalAccepted1078 : candidateIntervalCheck candidate1078 (14/25) (561/1000) piece1078=true := by decide +kernel
noncomputable def cell1078 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1078 accepted1078 (14/25) (561/1000) piece1078
    intervalAccepted1078 (fun t => piece_le_psi ⟨976,by decide +kernel⟩ t)
def piece1079 : AffinePiece := pieces[977]'(by decide +kernel)
theorem intervalAccepted1079 : candidateIntervalCheck candidate1079 (561/1000) (281/500) piece1079=true := by decide +kernel
noncomputable def cell1079 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1079 accepted1079 (561/1000) (281/500) piece1079
    intervalAccepted1079 (fun t => piece_le_psi ⟨977,by decide +kernel⟩ t)
def piece1080 : AffinePiece := pieces[978]'(by decide +kernel)
theorem intervalAccepted1080 : candidateIntervalCheck candidate1080 (281/500) (563/1000) piece1080=true := by decide +kernel
noncomputable def cell1080 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1080 accepted1080 (281/500) (563/1000) piece1080
    intervalAccepted1080 (fun t => piece_le_psi ⟨978,by decide +kernel⟩ t)
def piece1081 : AffinePiece := pieces[979]'(by decide +kernel)
theorem intervalAccepted1081 : candidateIntervalCheck candidate1081 (563/1000) (141/250) piece1081=true := by decide +kernel
noncomputable def cell1081 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1081 accepted1081 (563/1000) (141/250) piece1081
    intervalAccepted1081 (fun t => piece_le_psi ⟨979,by decide +kernel⟩ t)
def piece1082 : AffinePiece := pieces[980]'(by decide +kernel)
theorem intervalAccepted1082 : candidateIntervalCheck candidate1082 (141/250) (113/200) piece1082=true := by decide +kernel
noncomputable def cell1082 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1082 accepted1082 (141/250) (113/200) piece1082
    intervalAccepted1082 (fun t => piece_le_psi ⟨980,by decide +kernel⟩ t)
def piece1083 : AffinePiece := pieces[981]'(by decide +kernel)
theorem intervalAccepted1083 : candidateIntervalCheck candidate1083 (113/200) (283/500) piece1083=true := by decide +kernel
noncomputable def cell1083 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1083 accepted1083 (113/200) (283/500) piece1083
    intervalAccepted1083 (fun t => piece_le_psi ⟨981,by decide +kernel⟩ t)
def piece1084 : AffinePiece := pieces[982]'(by decide +kernel)
theorem intervalAccepted1084 : candidateIntervalCheck candidate1084 (283/500) (567/1000) piece1084=true := by decide +kernel
noncomputable def cell1084 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1084 accepted1084 (283/500) (567/1000) piece1084
    intervalAccepted1084 (fun t => piece_le_psi ⟨982,by decide +kernel⟩ t)
def piece1085 : AffinePiece := pieces[983]'(by decide +kernel)
theorem intervalAccepted1085 : candidateIntervalCheck candidate1085 (567/1000) (71/125) piece1085=true := by decide +kernel
noncomputable def cell1085 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1085 accepted1085 (567/1000) (71/125) piece1085
    intervalAccepted1085 (fun t => piece_le_psi ⟨983,by decide +kernel⟩ t)
def piece1086 : AffinePiece := pieces[984]'(by decide +kernel)
theorem intervalAccepted1086 : candidateIntervalCheck candidate1086 (71/125) (569/1000) piece1086=true := by decide +kernel
noncomputable def cell1086 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1086 accepted1086 (71/125) (569/1000) piece1086
    intervalAccepted1086 (fun t => piece_le_psi ⟨984,by decide +kernel⟩ t)
def piece1087 : AffinePiece := pieces[985]'(by decide +kernel)
theorem intervalAccepted1087 : candidateIntervalCheck candidate1087 (569/1000) (57/100) piece1087=true := by decide +kernel
noncomputable def cell1087 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1087 accepted1087 (569/1000) (57/100) piece1087
    intervalAccepted1087 (fun t => piece_le_psi ⟨985,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1072, cell1073, cell1074, cell1075, cell1076, cell1077, cell1078, cell1079, cell1080, cell1081, cell1082, cell1083, cell1084, cell1085, cell1086, cell1087]
theorem chainAccepted : spinCellChainCheck (277/500) (57/100) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (277/500) (57/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0067
