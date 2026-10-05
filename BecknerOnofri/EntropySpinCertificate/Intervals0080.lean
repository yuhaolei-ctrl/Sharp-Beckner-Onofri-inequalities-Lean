module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0080

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0080
open CandidateBatch0080 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1280 : AffinePiece := pieces[1178]'(by decide +kernel)
theorem intervalAccepted1280 : candidateIntervalCheck candidate1280 (381/500) (763/1000) piece1280=true := by decide +kernel
noncomputable def cell1280 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1280 accepted1280 (381/500) (763/1000) piece1280
    intervalAccepted1280 (fun t => piece_le_psi ⟨1178,by decide +kernel⟩ t)
def piece1281 : AffinePiece := pieces[1179]'(by decide +kernel)
theorem intervalAccepted1281 : candidateIntervalCheck candidate1281 (763/1000) (191/250) piece1281=true := by decide +kernel
noncomputable def cell1281 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1281 accepted1281 (763/1000) (191/250) piece1281
    intervalAccepted1281 (fun t => piece_le_psi ⟨1179,by decide +kernel⟩ t)
def piece1282 : AffinePiece := pieces[1180]'(by decide +kernel)
theorem intervalAccepted1282 : candidateIntervalCheck candidate1282 (191/250) (153/200) piece1282=true := by decide +kernel
noncomputable def cell1282 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1282 accepted1282 (191/250) (153/200) piece1282
    intervalAccepted1282 (fun t => piece_le_psi ⟨1180,by decide +kernel⟩ t)
def piece1283 : AffinePiece := pieces[1181]'(by decide +kernel)
theorem intervalAccepted1283 : candidateIntervalCheck candidate1283 (153/200) (383/500) piece1283=true := by decide +kernel
noncomputable def cell1283 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1283 accepted1283 (153/200) (383/500) piece1283
    intervalAccepted1283 (fun t => piece_le_psi ⟨1181,by decide +kernel⟩ t)
def piece1284 : AffinePiece := pieces[1182]'(by decide +kernel)
theorem intervalAccepted1284 : candidateIntervalCheck candidate1284 (383/500) (767/1000) piece1284=true := by decide +kernel
noncomputable def cell1284 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1284 accepted1284 (383/500) (767/1000) piece1284
    intervalAccepted1284 (fun t => piece_le_psi ⟨1182,by decide +kernel⟩ t)
def piece1285 : AffinePiece := pieces[1183]'(by decide +kernel)
theorem intervalAccepted1285 : candidateIntervalCheck candidate1285 (767/1000) (96/125) piece1285=true := by decide +kernel
noncomputable def cell1285 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1285 accepted1285 (767/1000) (96/125) piece1285
    intervalAccepted1285 (fun t => piece_le_psi ⟨1183,by decide +kernel⟩ t)
def piece1286 : AffinePiece := pieces[1184]'(by decide +kernel)
theorem intervalAccepted1286 : candidateIntervalCheck candidate1286 (96/125) (769/1000) piece1286=true := by decide +kernel
noncomputable def cell1286 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1286 accepted1286 (96/125) (769/1000) piece1286
    intervalAccepted1286 (fun t => piece_le_psi ⟨1184,by decide +kernel⟩ t)
def piece1287 : AffinePiece := pieces[1185]'(by decide +kernel)
theorem intervalAccepted1287 : candidateIntervalCheck candidate1287 (769/1000) (77/100) piece1287=true := by decide +kernel
noncomputable def cell1287 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1287 accepted1287 (769/1000) (77/100) piece1287
    intervalAccepted1287 (fun t => piece_le_psi ⟨1185,by decide +kernel⟩ t)
def piece1288 : AffinePiece := pieces[1186]'(by decide +kernel)
theorem intervalAccepted1288 : candidateIntervalCheck candidate1288 (77/100) (771/1000) piece1288=true := by decide +kernel
noncomputable def cell1288 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1288 accepted1288 (77/100) (771/1000) piece1288
    intervalAccepted1288 (fun t => piece_le_psi ⟨1186,by decide +kernel⟩ t)
def piece1289 : AffinePiece := pieces[1187]'(by decide +kernel)
theorem intervalAccepted1289 : candidateIntervalCheck candidate1289 (771/1000) (193/250) piece1289=true := by decide +kernel
noncomputable def cell1289 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1289 accepted1289 (771/1000) (193/250) piece1289
    intervalAccepted1289 (fun t => piece_le_psi ⟨1187,by decide +kernel⟩ t)
def piece1290 : AffinePiece := pieces[1188]'(by decide +kernel)
theorem intervalAccepted1290 : candidateIntervalCheck candidate1290 (193/250) (773/1000) piece1290=true := by decide +kernel
noncomputable def cell1290 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1290 accepted1290 (193/250) (773/1000) piece1290
    intervalAccepted1290 (fun t => piece_le_psi ⟨1188,by decide +kernel⟩ t)
def piece1291 : AffinePiece := pieces[1189]'(by decide +kernel)
theorem intervalAccepted1291 : candidateIntervalCheck candidate1291 (773/1000) (387/500) piece1291=true := by decide +kernel
noncomputable def cell1291 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1291 accepted1291 (773/1000) (387/500) piece1291
    intervalAccepted1291 (fun t => piece_le_psi ⟨1189,by decide +kernel⟩ t)
def piece1292 : AffinePiece := pieces[1190]'(by decide +kernel)
theorem intervalAccepted1292 : candidateIntervalCheck candidate1292 (387/500) (31/40) piece1292=true := by decide +kernel
noncomputable def cell1292 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1292 accepted1292 (387/500) (31/40) piece1292
    intervalAccepted1292 (fun t => piece_le_psi ⟨1190,by decide +kernel⟩ t)
def piece1293 : AffinePiece := pieces[1191]'(by decide +kernel)
theorem intervalAccepted1293 : candidateIntervalCheck candidate1293 (31/40) (97/125) piece1293=true := by decide +kernel
noncomputable def cell1293 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1293 accepted1293 (31/40) (97/125) piece1293
    intervalAccepted1293 (fun t => piece_le_psi ⟨1191,by decide +kernel⟩ t)
def piece1294 : AffinePiece := pieces[1192]'(by decide +kernel)
theorem intervalAccepted1294 : candidateIntervalCheck candidate1294 (97/125) (777/1000) piece1294=true := by decide +kernel
noncomputable def cell1294 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1294 accepted1294 (97/125) (777/1000) piece1294
    intervalAccepted1294 (fun t => piece_le_psi ⟨1192,by decide +kernel⟩ t)
def piece1295 : AffinePiece := pieces[1193]'(by decide +kernel)
theorem intervalAccepted1295 : candidateIntervalCheck candidate1295 (777/1000) (389/500) piece1295=true := by decide +kernel
noncomputable def cell1295 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1295 accepted1295 (777/1000) (389/500) piece1295
    intervalAccepted1295 (fun t => piece_le_psi ⟨1193,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1280, cell1281, cell1282, cell1283, cell1284, cell1285, cell1286, cell1287, cell1288, cell1289, cell1290, cell1291, cell1292, cell1293, cell1294, cell1295]
theorem chainAccepted : spinCellChainCheck (381/500) (389/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (381/500) (389/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0080
