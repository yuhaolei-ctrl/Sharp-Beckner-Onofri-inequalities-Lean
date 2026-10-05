import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0088
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0088
open CandidateBatch0088 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1408 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1408 : candidateIntervalCheck candidate1408 (833/1000) (8331/10000) piece1408=true := by decide +kernel
noncomputable def cell1408 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1408 accepted1408 (833/1000) (8331/10000) piece1408
    intervalAccepted1408 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1409 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1409 : candidateIntervalCheck candidate1409 (8331/10000) (2083/2500) piece1409=true := by decide +kernel
noncomputable def cell1409 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1409 accepted1409 (8331/10000) (2083/2500) piece1409
    intervalAccepted1409 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1410 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1410 : candidateIntervalCheck candidate1410 (2083/2500) (8333/10000) piece1410=true := by decide +kernel
noncomputable def cell1410 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1410 accepted1410 (2083/2500) (8333/10000) piece1410
    intervalAccepted1410 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1411 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1411 : candidateIntervalCheck candidate1411 (8333/10000) (4167/5000) piece1411=true := by decide +kernel
noncomputable def cell1411 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1411 accepted1411 (8333/10000) (4167/5000) piece1411
    intervalAccepted1411 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1412 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1412 : candidateIntervalCheck candidate1412 (4167/5000) (1667/2000) piece1412=true := by decide +kernel
noncomputable def cell1412 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1412 accepted1412 (4167/5000) (1667/2000) piece1412
    intervalAccepted1412 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1413 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1413 : candidateIntervalCheck candidate1413 (1667/2000) (521/625) piece1413=true := by decide +kernel
noncomputable def cell1413 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1413 accepted1413 (1667/2000) (521/625) piece1413
    intervalAccepted1413 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1414 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1414 : candidateIntervalCheck candidate1414 (521/625) (8337/10000) piece1414=true := by decide +kernel
noncomputable def cell1414 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1414 accepted1414 (521/625) (8337/10000) piece1414
    intervalAccepted1414 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1415 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1415 : candidateIntervalCheck candidate1415 (8337/10000) (4169/5000) piece1415=true := by decide +kernel
noncomputable def cell1415 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1415 accepted1415 (8337/10000) (4169/5000) piece1415
    intervalAccepted1415 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1416 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1416 : candidateIntervalCheck candidate1416 (4169/5000) (8339/10000) piece1416=true := by decide +kernel
noncomputable def cell1416 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1416 accepted1416 (4169/5000) (8339/10000) piece1416
    intervalAccepted1416 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1417 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1417 : candidateIntervalCheck candidate1417 (8339/10000) (417/500) piece1417=true := by decide +kernel
noncomputable def cell1417 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1417 accepted1417 (8339/10000) (417/500) piece1417
    intervalAccepted1417 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1418 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1418 : candidateIntervalCheck candidate1418 (417/500) (8341/10000) piece1418=true := by decide +kernel
noncomputable def cell1418 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1418 accepted1418 (417/500) (8341/10000) piece1418
    intervalAccepted1418 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1419 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1419 : candidateIntervalCheck candidate1419 (8341/10000) (4171/5000) piece1419=true := by decide +kernel
noncomputable def cell1419 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1419 accepted1419 (8341/10000) (4171/5000) piece1419
    intervalAccepted1419 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1420 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1420 : candidateIntervalCheck candidate1420 (4171/5000) (8343/10000) piece1420=true := by decide +kernel
noncomputable def cell1420 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1420 accepted1420 (4171/5000) (8343/10000) piece1420
    intervalAccepted1420 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1421 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1421 : candidateIntervalCheck candidate1421 (8343/10000) (1043/1250) piece1421=true := by decide +kernel
noncomputable def cell1421 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1421 accepted1421 (8343/10000) (1043/1250) piece1421
    intervalAccepted1421 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1422 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1422 : candidateIntervalCheck candidate1422 (1043/1250) (1669/2000) piece1422=true := by decide +kernel
noncomputable def cell1422 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1422 accepted1422 (1043/1250) (1669/2000) piece1422
    intervalAccepted1422 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1423 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1423 : candidateIntervalCheck candidate1423 (1669/2000) (4173/5000) piece1423=true := by decide +kernel
noncomputable def cell1423 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1423 accepted1423 (1669/2000) (4173/5000) piece1423
    intervalAccepted1423 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1408, cell1409, cell1410, cell1411, cell1412, cell1413, cell1414, cell1415, cell1416, cell1417, cell1418, cell1419, cell1420, cell1421, cell1422, cell1423]
theorem chainAccepted : spinCellChainCheck (833/1000) (4173/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (833/1000) (4173/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0088
