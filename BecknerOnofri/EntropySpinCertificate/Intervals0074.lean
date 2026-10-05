import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0074
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0074
open CandidateBatch0074 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1184 : AffinePiece := pieces[1082]'(by decide +kernel)
theorem intervalAccepted1184 : candidateIntervalCheck candidate1184 (333/500) (667/1000) piece1184=true := by decide +kernel
noncomputable def cell1184 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1184 accepted1184 (333/500) (667/1000) piece1184
    intervalAccepted1184 (fun t => piece_le_psi ⟨1082,by decide +kernel⟩ t)
def piece1185 : AffinePiece := pieces[1083]'(by decide +kernel)
theorem intervalAccepted1185 : candidateIntervalCheck candidate1185 (667/1000) (167/250) piece1185=true := by decide +kernel
noncomputable def cell1185 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1185 accepted1185 (667/1000) (167/250) piece1185
    intervalAccepted1185 (fun t => piece_le_psi ⟨1083,by decide +kernel⟩ t)
def piece1186 : AffinePiece := pieces[1084]'(by decide +kernel)
theorem intervalAccepted1186 : candidateIntervalCheck candidate1186 (167/250) (669/1000) piece1186=true := by decide +kernel
noncomputable def cell1186 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1186 accepted1186 (167/250) (669/1000) piece1186
    intervalAccepted1186 (fun t => piece_le_psi ⟨1084,by decide +kernel⟩ t)
def piece1187 : AffinePiece := pieces[1085]'(by decide +kernel)
theorem intervalAccepted1187 : candidateIntervalCheck candidate1187 (669/1000) (67/100) piece1187=true := by decide +kernel
noncomputable def cell1187 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1187 accepted1187 (669/1000) (67/100) piece1187
    intervalAccepted1187 (fun t => piece_le_psi ⟨1085,by decide +kernel⟩ t)
def piece1188 : AffinePiece := pieces[1086]'(by decide +kernel)
theorem intervalAccepted1188 : candidateIntervalCheck candidate1188 (67/100) (671/1000) piece1188=true := by decide +kernel
noncomputable def cell1188 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1188 accepted1188 (67/100) (671/1000) piece1188
    intervalAccepted1188 (fun t => piece_le_psi ⟨1086,by decide +kernel⟩ t)
def piece1189 : AffinePiece := pieces[1087]'(by decide +kernel)
theorem intervalAccepted1189 : candidateIntervalCheck candidate1189 (671/1000) (84/125) piece1189=true := by decide +kernel
noncomputable def cell1189 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1189 accepted1189 (671/1000) (84/125) piece1189
    intervalAccepted1189 (fun t => piece_le_psi ⟨1087,by decide +kernel⟩ t)
def piece1190 : AffinePiece := pieces[1088]'(by decide +kernel)
theorem intervalAccepted1190 : candidateIntervalCheck candidate1190 (84/125) (673/1000) piece1190=true := by decide +kernel
noncomputable def cell1190 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1190 accepted1190 (84/125) (673/1000) piece1190
    intervalAccepted1190 (fun t => piece_le_psi ⟨1088,by decide +kernel⟩ t)
def piece1191 : AffinePiece := pieces[1089]'(by decide +kernel)
theorem intervalAccepted1191 : candidateIntervalCheck candidate1191 (673/1000) (337/500) piece1191=true := by decide +kernel
noncomputable def cell1191 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1191 accepted1191 (673/1000) (337/500) piece1191
    intervalAccepted1191 (fun t => piece_le_psi ⟨1089,by decide +kernel⟩ t)
def piece1192 : AffinePiece := pieces[1090]'(by decide +kernel)
theorem intervalAccepted1192 : candidateIntervalCheck candidate1192 (337/500) (27/40) piece1192=true := by decide +kernel
noncomputable def cell1192 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1192 accepted1192 (337/500) (27/40) piece1192
    intervalAccepted1192 (fun t => piece_le_psi ⟨1090,by decide +kernel⟩ t)
def piece1193 : AffinePiece := pieces[1091]'(by decide +kernel)
theorem intervalAccepted1193 : candidateIntervalCheck candidate1193 (27/40) (169/250) piece1193=true := by decide +kernel
noncomputable def cell1193 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1193 accepted1193 (27/40) (169/250) piece1193
    intervalAccepted1193 (fun t => piece_le_psi ⟨1091,by decide +kernel⟩ t)
def piece1194 : AffinePiece := pieces[1092]'(by decide +kernel)
theorem intervalAccepted1194 : candidateIntervalCheck candidate1194 (169/250) (677/1000) piece1194=true := by decide +kernel
noncomputable def cell1194 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1194 accepted1194 (169/250) (677/1000) piece1194
    intervalAccepted1194 (fun t => piece_le_psi ⟨1092,by decide +kernel⟩ t)
def piece1195 : AffinePiece := pieces[1093]'(by decide +kernel)
theorem intervalAccepted1195 : candidateIntervalCheck candidate1195 (677/1000) (339/500) piece1195=true := by decide +kernel
noncomputable def cell1195 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1195 accepted1195 (677/1000) (339/500) piece1195
    intervalAccepted1195 (fun t => piece_le_psi ⟨1093,by decide +kernel⟩ t)
def piece1196 : AffinePiece := pieces[1094]'(by decide +kernel)
theorem intervalAccepted1196 : candidateIntervalCheck candidate1196 (339/500) (679/1000) piece1196=true := by decide +kernel
noncomputable def cell1196 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1196 accepted1196 (339/500) (679/1000) piece1196
    intervalAccepted1196 (fun t => piece_le_psi ⟨1094,by decide +kernel⟩ t)
def piece1197 : AffinePiece := pieces[1095]'(by decide +kernel)
theorem intervalAccepted1197 : candidateIntervalCheck candidate1197 (679/1000) (17/25) piece1197=true := by decide +kernel
noncomputable def cell1197 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1197 accepted1197 (679/1000) (17/25) piece1197
    intervalAccepted1197 (fun t => piece_le_psi ⟨1095,by decide +kernel⟩ t)
def piece1198 : AffinePiece := pieces[1096]'(by decide +kernel)
theorem intervalAccepted1198 : candidateIntervalCheck candidate1198 (17/25) (681/1000) piece1198=true := by decide +kernel
noncomputable def cell1198 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1198 accepted1198 (17/25) (681/1000) piece1198
    intervalAccepted1198 (fun t => piece_le_psi ⟨1096,by decide +kernel⟩ t)
def piece1199 : AffinePiece := pieces[1097]'(by decide +kernel)
theorem intervalAccepted1199 : candidateIntervalCheck candidate1199 (681/1000) (341/500) piece1199=true := by decide +kernel
noncomputable def cell1199 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1199 accepted1199 (681/1000) (341/500) piece1199
    intervalAccepted1199 (fun t => piece_le_psi ⟨1097,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1184, cell1185, cell1186, cell1187, cell1188, cell1189, cell1190, cell1191, cell1192, cell1193, cell1194, cell1195, cell1196, cell1197, cell1198, cell1199]
theorem chainAccepted : spinCellChainCheck (333/500) (341/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (333/500) (341/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0074
