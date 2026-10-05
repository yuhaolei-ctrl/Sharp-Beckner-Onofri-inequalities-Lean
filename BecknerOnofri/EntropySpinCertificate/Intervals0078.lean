module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0078

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0078
open CandidateBatch0078 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1248 : AffinePiece := pieces[1146]'(by decide +kernel)
theorem intervalAccepted1248 : candidateIntervalCheck candidate1248 (73/100) (731/1000) piece1248=true := by decide +kernel
noncomputable def cell1248 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1248 accepted1248 (73/100) (731/1000) piece1248
    intervalAccepted1248 (fun t => piece_le_psi ⟨1146,by decide +kernel⟩ t)
def piece1249 : AffinePiece := pieces[1147]'(by decide +kernel)
theorem intervalAccepted1249 : candidateIntervalCheck candidate1249 (731/1000) (183/250) piece1249=true := by decide +kernel
noncomputable def cell1249 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1249 accepted1249 (731/1000) (183/250) piece1249
    intervalAccepted1249 (fun t => piece_le_psi ⟨1147,by decide +kernel⟩ t)
def piece1250 : AffinePiece := pieces[1148]'(by decide +kernel)
theorem intervalAccepted1250 : candidateIntervalCheck candidate1250 (183/250) (733/1000) piece1250=true := by decide +kernel
noncomputable def cell1250 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1250 accepted1250 (183/250) (733/1000) piece1250
    intervalAccepted1250 (fun t => piece_le_psi ⟨1148,by decide +kernel⟩ t)
def piece1251 : AffinePiece := pieces[1149]'(by decide +kernel)
theorem intervalAccepted1251 : candidateIntervalCheck candidate1251 (733/1000) (367/500) piece1251=true := by decide +kernel
noncomputable def cell1251 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1251 accepted1251 (733/1000) (367/500) piece1251
    intervalAccepted1251 (fun t => piece_le_psi ⟨1149,by decide +kernel⟩ t)
def piece1252 : AffinePiece := pieces[1150]'(by decide +kernel)
theorem intervalAccepted1252 : candidateIntervalCheck candidate1252 (367/500) (147/200) piece1252=true := by decide +kernel
noncomputable def cell1252 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1252 accepted1252 (367/500) (147/200) piece1252
    intervalAccepted1252 (fun t => piece_le_psi ⟨1150,by decide +kernel⟩ t)
def piece1253 : AffinePiece := pieces[1151]'(by decide +kernel)
theorem intervalAccepted1253 : candidateIntervalCheck candidate1253 (147/200) (92/125) piece1253=true := by decide +kernel
noncomputable def cell1253 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1253 accepted1253 (147/200) (92/125) piece1253
    intervalAccepted1253 (fun t => piece_le_psi ⟨1151,by decide +kernel⟩ t)
def piece1254 : AffinePiece := pieces[1152]'(by decide +kernel)
theorem intervalAccepted1254 : candidateIntervalCheck candidate1254 (92/125) (737/1000) piece1254=true := by decide +kernel
noncomputable def cell1254 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1254 accepted1254 (92/125) (737/1000) piece1254
    intervalAccepted1254 (fun t => piece_le_psi ⟨1152,by decide +kernel⟩ t)
def piece1255 : AffinePiece := pieces[1153]'(by decide +kernel)
theorem intervalAccepted1255 : candidateIntervalCheck candidate1255 (737/1000) (369/500) piece1255=true := by decide +kernel
noncomputable def cell1255 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1255 accepted1255 (737/1000) (369/500) piece1255
    intervalAccepted1255 (fun t => piece_le_psi ⟨1153,by decide +kernel⟩ t)
def piece1256 : AffinePiece := pieces[1154]'(by decide +kernel)
theorem intervalAccepted1256 : candidateIntervalCheck candidate1256 (369/500) (739/1000) piece1256=true := by decide +kernel
noncomputable def cell1256 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1256 accepted1256 (369/500) (739/1000) piece1256
    intervalAccepted1256 (fun t => piece_le_psi ⟨1154,by decide +kernel⟩ t)
def piece1257 : AffinePiece := pieces[1155]'(by decide +kernel)
theorem intervalAccepted1257 : candidateIntervalCheck candidate1257 (739/1000) (37/50) piece1257=true := by decide +kernel
noncomputable def cell1257 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1257 accepted1257 (739/1000) (37/50) piece1257
    intervalAccepted1257 (fun t => piece_le_psi ⟨1155,by decide +kernel⟩ t)
def piece1258 : AffinePiece := pieces[1156]'(by decide +kernel)
theorem intervalAccepted1258 : candidateIntervalCheck candidate1258 (37/50) (741/1000) piece1258=true := by decide +kernel
noncomputable def cell1258 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1258 accepted1258 (37/50) (741/1000) piece1258
    intervalAccepted1258 (fun t => piece_le_psi ⟨1156,by decide +kernel⟩ t)
def piece1259 : AffinePiece := pieces[1157]'(by decide +kernel)
theorem intervalAccepted1259 : candidateIntervalCheck candidate1259 (741/1000) (371/500) piece1259=true := by decide +kernel
noncomputable def cell1259 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1259 accepted1259 (741/1000) (371/500) piece1259
    intervalAccepted1259 (fun t => piece_le_psi ⟨1157,by decide +kernel⟩ t)
def piece1260 : AffinePiece := pieces[1158]'(by decide +kernel)
theorem intervalAccepted1260 : candidateIntervalCheck candidate1260 (371/500) (743/1000) piece1260=true := by decide +kernel
noncomputable def cell1260 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1260 accepted1260 (371/500) (743/1000) piece1260
    intervalAccepted1260 (fun t => piece_le_psi ⟨1158,by decide +kernel⟩ t)
def piece1261 : AffinePiece := pieces[1159]'(by decide +kernel)
theorem intervalAccepted1261 : candidateIntervalCheck candidate1261 (743/1000) (93/125) piece1261=true := by decide +kernel
noncomputable def cell1261 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1261 accepted1261 (743/1000) (93/125) piece1261
    intervalAccepted1261 (fun t => piece_le_psi ⟨1159,by decide +kernel⟩ t)
def piece1262 : AffinePiece := pieces[1160]'(by decide +kernel)
theorem intervalAccepted1262 : candidateIntervalCheck candidate1262 (93/125) (149/200) piece1262=true := by decide +kernel
noncomputable def cell1262 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1262 accepted1262 (93/125) (149/200) piece1262
    intervalAccepted1262 (fun t => piece_le_psi ⟨1160,by decide +kernel⟩ t)
def piece1263 : AffinePiece := pieces[1161]'(by decide +kernel)
theorem intervalAccepted1263 : candidateIntervalCheck candidate1263 (149/200) (373/500) piece1263=true := by decide +kernel
noncomputable def cell1263 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1263 accepted1263 (149/200) (373/500) piece1263
    intervalAccepted1263 (fun t => piece_le_psi ⟨1161,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1248, cell1249, cell1250, cell1251, cell1252, cell1253, cell1254, cell1255, cell1256, cell1257, cell1258, cell1259, cell1260, cell1261, cell1262, cell1263]
theorem chainAccepted : spinCellChainCheck (73/100) (373/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (73/100) (373/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0078
