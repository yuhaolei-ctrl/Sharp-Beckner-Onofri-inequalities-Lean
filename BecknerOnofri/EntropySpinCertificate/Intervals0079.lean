import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0079
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0079
open CandidateBatch0079 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1264 : AffinePiece := pieces[1162]'(by decide +kernel)
theorem intervalAccepted1264 : candidateIntervalCheck candidate1264 (373/500) (747/1000) piece1264=true := by decide +kernel
noncomputable def cell1264 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1264 accepted1264 (373/500) (747/1000) piece1264
    intervalAccepted1264 (fun t => piece_le_psi ⟨1162,by decide +kernel⟩ t)
def piece1265 : AffinePiece := pieces[1163]'(by decide +kernel)
theorem intervalAccepted1265 : candidateIntervalCheck candidate1265 (747/1000) (187/250) piece1265=true := by decide +kernel
noncomputable def cell1265 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1265 accepted1265 (747/1000) (187/250) piece1265
    intervalAccepted1265 (fun t => piece_le_psi ⟨1163,by decide +kernel⟩ t)
def piece1266 : AffinePiece := pieces[1164]'(by decide +kernel)
theorem intervalAccepted1266 : candidateIntervalCheck candidate1266 (187/250) (749/1000) piece1266=true := by decide +kernel
noncomputable def cell1266 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1266 accepted1266 (187/250) (749/1000) piece1266
    intervalAccepted1266 (fun t => piece_le_psi ⟨1164,by decide +kernel⟩ t)
def piece1267 : AffinePiece := pieces[1165]'(by decide +kernel)
theorem intervalAccepted1267 : candidateIntervalCheck candidate1267 (749/1000) (3/4) piece1267=true := by decide +kernel
noncomputable def cell1267 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1267 accepted1267 (749/1000) (3/4) piece1267
    intervalAccepted1267 (fun t => piece_le_psi ⟨1165,by decide +kernel⟩ t)
def piece1268 : AffinePiece := pieces[1166]'(by decide +kernel)
theorem intervalAccepted1268 : candidateIntervalCheck candidate1268 (3/4) (751/1000) piece1268=true := by decide +kernel
noncomputable def cell1268 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1268 accepted1268 (3/4) (751/1000) piece1268
    intervalAccepted1268 (fun t => piece_le_psi ⟨1166,by decide +kernel⟩ t)
def piece1269 : AffinePiece := pieces[1167]'(by decide +kernel)
theorem intervalAccepted1269 : candidateIntervalCheck candidate1269 (751/1000) (94/125) piece1269=true := by decide +kernel
noncomputable def cell1269 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1269 accepted1269 (751/1000) (94/125) piece1269
    intervalAccepted1269 (fun t => piece_le_psi ⟨1167,by decide +kernel⟩ t)
def piece1270 : AffinePiece := pieces[1168]'(by decide +kernel)
theorem intervalAccepted1270 : candidateIntervalCheck candidate1270 (94/125) (753/1000) piece1270=true := by decide +kernel
noncomputable def cell1270 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1270 accepted1270 (94/125) (753/1000) piece1270
    intervalAccepted1270 (fun t => piece_le_psi ⟨1168,by decide +kernel⟩ t)
def piece1271 : AffinePiece := pieces[1169]'(by decide +kernel)
theorem intervalAccepted1271 : candidateIntervalCheck candidate1271 (753/1000) (377/500) piece1271=true := by decide +kernel
noncomputable def cell1271 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1271 accepted1271 (753/1000) (377/500) piece1271
    intervalAccepted1271 (fun t => piece_le_psi ⟨1169,by decide +kernel⟩ t)
def piece1272 : AffinePiece := pieces[1170]'(by decide +kernel)
theorem intervalAccepted1272 : candidateIntervalCheck candidate1272 (377/500) (151/200) piece1272=true := by decide +kernel
noncomputable def cell1272 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1272 accepted1272 (377/500) (151/200) piece1272
    intervalAccepted1272 (fun t => piece_le_psi ⟨1170,by decide +kernel⟩ t)
def piece1273 : AffinePiece := pieces[1171]'(by decide +kernel)
theorem intervalAccepted1273 : candidateIntervalCheck candidate1273 (151/200) (189/250) piece1273=true := by decide +kernel
noncomputable def cell1273 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1273 accepted1273 (151/200) (189/250) piece1273
    intervalAccepted1273 (fun t => piece_le_psi ⟨1171,by decide +kernel⟩ t)
def piece1274 : AffinePiece := pieces[1172]'(by decide +kernel)
theorem intervalAccepted1274 : candidateIntervalCheck candidate1274 (189/250) (757/1000) piece1274=true := by decide +kernel
noncomputable def cell1274 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1274 accepted1274 (189/250) (757/1000) piece1274
    intervalAccepted1274 (fun t => piece_le_psi ⟨1172,by decide +kernel⟩ t)
def piece1275 : AffinePiece := pieces[1173]'(by decide +kernel)
theorem intervalAccepted1275 : candidateIntervalCheck candidate1275 (757/1000) (379/500) piece1275=true := by decide +kernel
noncomputable def cell1275 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1275 accepted1275 (757/1000) (379/500) piece1275
    intervalAccepted1275 (fun t => piece_le_psi ⟨1173,by decide +kernel⟩ t)
def piece1276 : AffinePiece := pieces[1174]'(by decide +kernel)
theorem intervalAccepted1276 : candidateIntervalCheck candidate1276 (379/500) (759/1000) piece1276=true := by decide +kernel
noncomputable def cell1276 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1276 accepted1276 (379/500) (759/1000) piece1276
    intervalAccepted1276 (fun t => piece_le_psi ⟨1174,by decide +kernel⟩ t)
def piece1277 : AffinePiece := pieces[1175]'(by decide +kernel)
theorem intervalAccepted1277 : candidateIntervalCheck candidate1277 (759/1000) (19/25) piece1277=true := by decide +kernel
noncomputable def cell1277 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1277 accepted1277 (759/1000) (19/25) piece1277
    intervalAccepted1277 (fun t => piece_le_psi ⟨1175,by decide +kernel⟩ t)
def piece1278 : AffinePiece := pieces[1176]'(by decide +kernel)
theorem intervalAccepted1278 : candidateIntervalCheck candidate1278 (19/25) (761/1000) piece1278=true := by decide +kernel
noncomputable def cell1278 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1278 accepted1278 (19/25) (761/1000) piece1278
    intervalAccepted1278 (fun t => piece_le_psi ⟨1176,by decide +kernel⟩ t)
def piece1279 : AffinePiece := pieces[1177]'(by decide +kernel)
theorem intervalAccepted1279 : candidateIntervalCheck candidate1279 (761/1000) (381/500) piece1279=true := by decide +kernel
noncomputable def cell1279 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1279 accepted1279 (761/1000) (381/500) piece1279
    intervalAccepted1279 (fun t => piece_le_psi ⟨1177,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1264, cell1265, cell1266, cell1267, cell1268, cell1269, cell1270, cell1271, cell1272, cell1273, cell1274, cell1275, cell1276, cell1277, cell1278, cell1279]
theorem chainAccepted : spinCellChainCheck (373/500) (381/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (373/500) (381/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0079
