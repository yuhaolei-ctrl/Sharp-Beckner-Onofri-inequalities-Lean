import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0084
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0084
open CandidateBatch0084 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1344 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1344 : candidateIntervalCheck candidate1344 (813/1000) (1627/2000) piece1344=true := by decide +kernel
noncomputable def cell1344 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1344 accepted1344 (813/1000) (1627/2000) piece1344
    intervalAccepted1344 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1345 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1345 : candidateIntervalCheck candidate1345 (1627/2000) (407/500) piece1345=true := by decide +kernel
noncomputable def cell1345 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1345 accepted1345 (1627/2000) (407/500) piece1345
    intervalAccepted1345 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1346 : AffinePiece := pieces[1217]'(by decide +kernel)
theorem intervalAccepted1346 : candidateIntervalCheck candidate1346 (407/500) (1629/2000) piece1346=true := by decide +kernel
noncomputable def cell1346 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1346 accepted1346 (407/500) (1629/2000) piece1346
    intervalAccepted1346 (fun t => piece_le_psi ⟨1217,by decide +kernel⟩ t)
def piece1347 : AffinePiece := pieces[1218]'(by decide +kernel)
theorem intervalAccepted1347 : candidateIntervalCheck candidate1347 (1629/2000) (163/200) piece1347=true := by decide +kernel
noncomputable def cell1347 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1347 accepted1347 (1629/2000) (163/200) piece1347
    intervalAccepted1347 (fun t => piece_le_psi ⟨1218,by decide +kernel⟩ t)
def piece1348 : AffinePiece := pieces[1219]'(by decide +kernel)
theorem intervalAccepted1348 : candidateIntervalCheck candidate1348 (163/200) (1631/2000) piece1348=true := by decide +kernel
noncomputable def cell1348 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1348 accepted1348 (163/200) (1631/2000) piece1348
    intervalAccepted1348 (fun t => piece_le_psi ⟨1219,by decide +kernel⟩ t)
def piece1349 : AffinePiece := pieces[1220]'(by decide +kernel)
theorem intervalAccepted1349 : candidateIntervalCheck candidate1349 (1631/2000) (102/125) piece1349=true := by decide +kernel
noncomputable def cell1349 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1349 accepted1349 (1631/2000) (102/125) piece1349
    intervalAccepted1349 (fun t => piece_le_psi ⟨1220,by decide +kernel⟩ t)
def piece1350 : AffinePiece := pieces[1221]'(by decide +kernel)
theorem intervalAccepted1350 : candidateIntervalCheck candidate1350 (102/125) (1633/2000) piece1350=true := by decide +kernel
noncomputable def cell1350 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1350 accepted1350 (102/125) (1633/2000) piece1350
    intervalAccepted1350 (fun t => piece_le_psi ⟨1221,by decide +kernel⟩ t)
def piece1351 : AffinePiece := pieces[1222]'(by decide +kernel)
theorem intervalAccepted1351 : candidateIntervalCheck candidate1351 (1633/2000) (817/1000) piece1351=true := by decide +kernel
noncomputable def cell1351 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1351 accepted1351 (1633/2000) (817/1000) piece1351
    intervalAccepted1351 (fun t => piece_le_psi ⟨1222,by decide +kernel⟩ t)
def piece1352 : AffinePiece := pieces[1223]'(by decide +kernel)
theorem intervalAccepted1352 : candidateIntervalCheck candidate1352 (817/1000) (327/400) piece1352=true := by decide +kernel
noncomputable def cell1352 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1352 accepted1352 (817/1000) (327/400) piece1352
    intervalAccepted1352 (fun t => piece_le_psi ⟨1223,by decide +kernel⟩ t)
def piece1353 : AffinePiece := pieces[1224]'(by decide +kernel)
theorem intervalAccepted1353 : candidateIntervalCheck candidate1353 (327/400) (409/500) piece1353=true := by decide +kernel
noncomputable def cell1353 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1353 accepted1353 (327/400) (409/500) piece1353
    intervalAccepted1353 (fun t => piece_le_psi ⟨1224,by decide +kernel⟩ t)
def piece1354 : AffinePiece := pieces[1225]'(by decide +kernel)
theorem intervalAccepted1354 : candidateIntervalCheck candidate1354 (409/500) (1637/2000) piece1354=true := by decide +kernel
noncomputable def cell1354 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1354 accepted1354 (409/500) (1637/2000) piece1354
    intervalAccepted1354 (fun t => piece_le_psi ⟨1225,by decide +kernel⟩ t)
def piece1355 : AffinePiece := pieces[1226]'(by decide +kernel)
theorem intervalAccepted1355 : candidateIntervalCheck candidate1355 (1637/2000) (819/1000) piece1355=true := by decide +kernel
noncomputable def cell1355 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1355 accepted1355 (1637/2000) (819/1000) piece1355
    intervalAccepted1355 (fun t => piece_le_psi ⟨1226,by decide +kernel⟩ t)
def piece1356 : AffinePiece := pieces[1227]'(by decide +kernel)
theorem intervalAccepted1356 : candidateIntervalCheck candidate1356 (819/1000) (1639/2000) piece1356=true := by decide +kernel
noncomputable def cell1356 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1356 accepted1356 (819/1000) (1639/2000) piece1356
    intervalAccepted1356 (fun t => piece_le_psi ⟨1227,by decide +kernel⟩ t)
def piece1357 : AffinePiece := pieces[1228]'(by decide +kernel)
theorem intervalAccepted1357 : candidateIntervalCheck candidate1357 (1639/2000) (41/50) piece1357=true := by decide +kernel
noncomputable def cell1357 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1357 accepted1357 (1639/2000) (41/50) piece1357
    intervalAccepted1357 (fun t => piece_le_psi ⟨1228,by decide +kernel⟩ t)
def piece1358 : AffinePiece := pieces[1229]'(by decide +kernel)
theorem intervalAccepted1358 : candidateIntervalCheck candidate1358 (41/50) (1641/2000) piece1358=true := by decide +kernel
noncomputable def cell1358 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1358 accepted1358 (41/50) (1641/2000) piece1358
    intervalAccepted1358 (fun t => piece_le_psi ⟨1229,by decide +kernel⟩ t)
def piece1359 : AffinePiece := pieces[1230]'(by decide +kernel)
theorem intervalAccepted1359 : candidateIntervalCheck candidate1359 (1641/2000) (821/1000) piece1359=true := by decide +kernel
noncomputable def cell1359 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1359 accepted1359 (1641/2000) (821/1000) piece1359
    intervalAccepted1359 (fun t => piece_le_psi ⟨1230,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1344, cell1345, cell1346, cell1347, cell1348, cell1349, cell1350, cell1351, cell1352, cell1353, cell1354, cell1355, cell1356, cell1357, cell1358, cell1359]
theorem chainAccepted : spinCellChainCheck (813/1000) (821/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (813/1000) (821/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0084
