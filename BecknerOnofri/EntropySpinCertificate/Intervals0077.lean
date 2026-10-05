import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0077
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0077
open CandidateBatch0077 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1232 : AffinePiece := pieces[1130]'(by decide +kernel)
theorem intervalAccepted1232 : candidateIntervalCheck candidate1232 (357/500) (143/200) piece1232=true := by decide +kernel
noncomputable def cell1232 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1232 accepted1232 (357/500) (143/200) piece1232
    intervalAccepted1232 (fun t => piece_le_psi ⟨1130,by decide +kernel⟩ t)
def piece1233 : AffinePiece := pieces[1131]'(by decide +kernel)
theorem intervalAccepted1233 : candidateIntervalCheck candidate1233 (143/200) (179/250) piece1233=true := by decide +kernel
noncomputable def cell1233 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1233 accepted1233 (143/200) (179/250) piece1233
    intervalAccepted1233 (fun t => piece_le_psi ⟨1131,by decide +kernel⟩ t)
def piece1234 : AffinePiece := pieces[1132]'(by decide +kernel)
theorem intervalAccepted1234 : candidateIntervalCheck candidate1234 (179/250) (717/1000) piece1234=true := by decide +kernel
noncomputable def cell1234 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1234 accepted1234 (179/250) (717/1000) piece1234
    intervalAccepted1234 (fun t => piece_le_psi ⟨1132,by decide +kernel⟩ t)
def piece1235 : AffinePiece := pieces[1133]'(by decide +kernel)
theorem intervalAccepted1235 : candidateIntervalCheck candidate1235 (717/1000) (359/500) piece1235=true := by decide +kernel
noncomputable def cell1235 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1235 accepted1235 (717/1000) (359/500) piece1235
    intervalAccepted1235 (fun t => piece_le_psi ⟨1133,by decide +kernel⟩ t)
def piece1236 : AffinePiece := pieces[1134]'(by decide +kernel)
theorem intervalAccepted1236 : candidateIntervalCheck candidate1236 (359/500) (719/1000) piece1236=true := by decide +kernel
noncomputable def cell1236 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1236 accepted1236 (359/500) (719/1000) piece1236
    intervalAccepted1236 (fun t => piece_le_psi ⟨1134,by decide +kernel⟩ t)
def piece1237 : AffinePiece := pieces[1135]'(by decide +kernel)
theorem intervalAccepted1237 : candidateIntervalCheck candidate1237 (719/1000) (18/25) piece1237=true := by decide +kernel
noncomputable def cell1237 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1237 accepted1237 (719/1000) (18/25) piece1237
    intervalAccepted1237 (fun t => piece_le_psi ⟨1135,by decide +kernel⟩ t)
def piece1238 : AffinePiece := pieces[1136]'(by decide +kernel)
theorem intervalAccepted1238 : candidateIntervalCheck candidate1238 (18/25) (721/1000) piece1238=true := by decide +kernel
noncomputable def cell1238 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1238 accepted1238 (18/25) (721/1000) piece1238
    intervalAccepted1238 (fun t => piece_le_psi ⟨1136,by decide +kernel⟩ t)
def piece1239 : AffinePiece := pieces[1137]'(by decide +kernel)
theorem intervalAccepted1239 : candidateIntervalCheck candidate1239 (721/1000) (361/500) piece1239=true := by decide +kernel
noncomputable def cell1239 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1239 accepted1239 (721/1000) (361/500) piece1239
    intervalAccepted1239 (fun t => piece_le_psi ⟨1137,by decide +kernel⟩ t)
def piece1240 : AffinePiece := pieces[1138]'(by decide +kernel)
theorem intervalAccepted1240 : candidateIntervalCheck candidate1240 (361/500) (723/1000) piece1240=true := by decide +kernel
noncomputable def cell1240 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1240 accepted1240 (361/500) (723/1000) piece1240
    intervalAccepted1240 (fun t => piece_le_psi ⟨1138,by decide +kernel⟩ t)
def piece1241 : AffinePiece := pieces[1139]'(by decide +kernel)
theorem intervalAccepted1241 : candidateIntervalCheck candidate1241 (723/1000) (181/250) piece1241=true := by decide +kernel
noncomputable def cell1241 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1241 accepted1241 (723/1000) (181/250) piece1241
    intervalAccepted1241 (fun t => piece_le_psi ⟨1139,by decide +kernel⟩ t)
def piece1242 : AffinePiece := pieces[1140]'(by decide +kernel)
theorem intervalAccepted1242 : candidateIntervalCheck candidate1242 (181/250) (29/40) piece1242=true := by decide +kernel
noncomputable def cell1242 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1242 accepted1242 (181/250) (29/40) piece1242
    intervalAccepted1242 (fun t => piece_le_psi ⟨1140,by decide +kernel⟩ t)
def piece1243 : AffinePiece := pieces[1141]'(by decide +kernel)
theorem intervalAccepted1243 : candidateIntervalCheck candidate1243 (29/40) (363/500) piece1243=true := by decide +kernel
noncomputable def cell1243 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1243 accepted1243 (29/40) (363/500) piece1243
    intervalAccepted1243 (fun t => piece_le_psi ⟨1141,by decide +kernel⟩ t)
def piece1244 : AffinePiece := pieces[1142]'(by decide +kernel)
theorem intervalAccepted1244 : candidateIntervalCheck candidate1244 (363/500) (727/1000) piece1244=true := by decide +kernel
noncomputable def cell1244 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1244 accepted1244 (363/500) (727/1000) piece1244
    intervalAccepted1244 (fun t => piece_le_psi ⟨1142,by decide +kernel⟩ t)
def piece1245 : AffinePiece := pieces[1143]'(by decide +kernel)
theorem intervalAccepted1245 : candidateIntervalCheck candidate1245 (727/1000) (91/125) piece1245=true := by decide +kernel
noncomputable def cell1245 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1245 accepted1245 (727/1000) (91/125) piece1245
    intervalAccepted1245 (fun t => piece_le_psi ⟨1143,by decide +kernel⟩ t)
def piece1246 : AffinePiece := pieces[1144]'(by decide +kernel)
theorem intervalAccepted1246 : candidateIntervalCheck candidate1246 (91/125) (729/1000) piece1246=true := by decide +kernel
noncomputable def cell1246 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1246 accepted1246 (91/125) (729/1000) piece1246
    intervalAccepted1246 (fun t => piece_le_psi ⟨1144,by decide +kernel⟩ t)
def piece1247 : AffinePiece := pieces[1145]'(by decide +kernel)
theorem intervalAccepted1247 : candidateIntervalCheck candidate1247 (729/1000) (73/100) piece1247=true := by decide +kernel
noncomputable def cell1247 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1247 accepted1247 (729/1000) (73/100) piece1247
    intervalAccepted1247 (fun t => piece_le_psi ⟨1145,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1232, cell1233, cell1234, cell1235, cell1236, cell1237, cell1238, cell1239, cell1240, cell1241, cell1242, cell1243, cell1244, cell1245, cell1246, cell1247]
theorem chainAccepted : spinCellChainCheck (357/500) (73/100) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (357/500) (73/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0077
