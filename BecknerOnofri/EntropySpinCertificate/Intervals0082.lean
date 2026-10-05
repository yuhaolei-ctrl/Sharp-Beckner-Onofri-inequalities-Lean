import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0082
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0082
open CandidateBatch0082 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1312 : AffinePiece := pieces[1210]'(by decide +kernel)
theorem intervalAccepted1312 : candidateIntervalCheck candidate1312 (397/500) (159/200) piece1312=true := by decide +kernel
noncomputable def cell1312 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1312 accepted1312 (397/500) (159/200) piece1312
    intervalAccepted1312 (fun t => piece_le_psi ⟨1210,by decide +kernel⟩ t)
def piece1313 : AffinePiece := pieces[1211]'(by decide +kernel)
theorem intervalAccepted1313 : candidateIntervalCheck candidate1313 (159/200) (199/250) piece1313=true := by decide +kernel
noncomputable def cell1313 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1313 accepted1313 (159/200) (199/250) piece1313
    intervalAccepted1313 (fun t => piece_le_psi ⟨1211,by decide +kernel⟩ t)
def piece1314 : AffinePiece := pieces[1212]'(by decide +kernel)
theorem intervalAccepted1314 : candidateIntervalCheck candidate1314 (199/250) (797/1000) piece1314=true := by decide +kernel
noncomputable def cell1314 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1314 accepted1314 (199/250) (797/1000) piece1314
    intervalAccepted1314 (fun t => piece_le_psi ⟨1212,by decide +kernel⟩ t)
def piece1315 : AffinePiece := pieces[1213]'(by decide +kernel)
theorem intervalAccepted1315 : candidateIntervalCheck candidate1315 (797/1000) (399/500) piece1315=true := by decide +kernel
noncomputable def cell1315 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1315 accepted1315 (797/1000) (399/500) piece1315
    intervalAccepted1315 (fun t => piece_le_psi ⟨1213,by decide +kernel⟩ t)
def piece1316 : AffinePiece := pieces[1214]'(by decide +kernel)
theorem intervalAccepted1316 : candidateIntervalCheck candidate1316 (399/500) (799/1000) piece1316=true := by decide +kernel
noncomputable def cell1316 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1316 accepted1316 (399/500) (799/1000) piece1316
    intervalAccepted1316 (fun t => piece_le_psi ⟨1214,by decide +kernel⟩ t)
def piece1317 : AffinePiece := pieces[1215]'(by decide +kernel)
theorem intervalAccepted1317 : candidateIntervalCheck candidate1317 (799/1000) (4/5) piece1317=true := by decide +kernel
noncomputable def cell1317 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1317 accepted1317 (799/1000) (4/5) piece1317
    intervalAccepted1317 (fun t => piece_le_psi ⟨1215,by decide +kernel⟩ t)
def piece1318 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1318 : candidateIntervalCheck candidate1318 (4/5) (1601/2000) piece1318=true := by decide +kernel
noncomputable def cell1318 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1318 accepted1318 (4/5) (1601/2000) piece1318
    intervalAccepted1318 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1319 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1319 : candidateIntervalCheck candidate1319 (1601/2000) (801/1000) piece1319=true := by decide +kernel
noncomputable def cell1319 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1319 accepted1319 (1601/2000) (801/1000) piece1319
    intervalAccepted1319 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1320 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1320 : candidateIntervalCheck candidate1320 (801/1000) (1603/2000) piece1320=true := by decide +kernel
noncomputable def cell1320 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1320 accepted1320 (801/1000) (1603/2000) piece1320
    intervalAccepted1320 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1321 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1321 : candidateIntervalCheck candidate1321 (1603/2000) (401/500) piece1321=true := by decide +kernel
noncomputable def cell1321 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1321 accepted1321 (1603/2000) (401/500) piece1321
    intervalAccepted1321 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1322 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1322 : candidateIntervalCheck candidate1322 (401/500) (321/400) piece1322=true := by decide +kernel
noncomputable def cell1322 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1322 accepted1322 (401/500) (321/400) piece1322
    intervalAccepted1322 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1323 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1323 : candidateIntervalCheck candidate1323 (321/400) (803/1000) piece1323=true := by decide +kernel
noncomputable def cell1323 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1323 accepted1323 (321/400) (803/1000) piece1323
    intervalAccepted1323 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1324 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1324 : candidateIntervalCheck candidate1324 (803/1000) (1607/2000) piece1324=true := by decide +kernel
noncomputable def cell1324 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1324 accepted1324 (803/1000) (1607/2000) piece1324
    intervalAccepted1324 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1325 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1325 : candidateIntervalCheck candidate1325 (1607/2000) (201/250) piece1325=true := by decide +kernel
noncomputable def cell1325 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1325 accepted1325 (1607/2000) (201/250) piece1325
    intervalAccepted1325 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1326 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1326 : candidateIntervalCheck candidate1326 (201/250) (1609/2000) piece1326=true := by decide +kernel
noncomputable def cell1326 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1326 accepted1326 (201/250) (1609/2000) piece1326
    intervalAccepted1326 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1327 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1327 : candidateIntervalCheck candidate1327 (1609/2000) (161/200) piece1327=true := by decide +kernel
noncomputable def cell1327 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1327 accepted1327 (1609/2000) (161/200) piece1327
    intervalAccepted1327 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1312, cell1313, cell1314, cell1315, cell1316, cell1317, cell1318, cell1319, cell1320, cell1321, cell1322, cell1323, cell1324, cell1325, cell1326, cell1327]
theorem chainAccepted : spinCellChainCheck (397/500) (161/200) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (397/500) (161/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0082
