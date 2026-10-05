import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0087
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0087
open CandidateBatch0087 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1392 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1392 : candidateIntervalCheck candidate1392 (4157/5000) (1663/2000) piece1392=true := by decide +kernel
noncomputable def cell1392 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1392 accepted1392 (4157/5000) (1663/2000) piece1392
    intervalAccepted1392 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1393 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1393 : candidateIntervalCheck candidate1393 (1663/2000) (2079/2500) piece1393=true := by decide +kernel
noncomputable def cell1393 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1393 accepted1393 (1663/2000) (2079/2500) piece1393
    intervalAccepted1393 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1394 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1394 : candidateIntervalCheck candidate1394 (2079/2500) (8317/10000) piece1394=true := by decide +kernel
noncomputable def cell1394 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1394 accepted1394 (2079/2500) (8317/10000) piece1394
    intervalAccepted1394 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1395 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1395 : candidateIntervalCheck candidate1395 (8317/10000) (4159/5000) piece1395=true := by decide +kernel
noncomputable def cell1395 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1395 accepted1395 (8317/10000) (4159/5000) piece1395
    intervalAccepted1395 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1396 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1396 : candidateIntervalCheck candidate1396 (4159/5000) (8319/10000) piece1396=true := by decide +kernel
noncomputable def cell1396 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1396 accepted1396 (4159/5000) (8319/10000) piece1396
    intervalAccepted1396 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1397 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1397 : candidateIntervalCheck candidate1397 (8319/10000) (104/125) piece1397=true := by decide +kernel
noncomputable def cell1397 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1397 accepted1397 (8319/10000) (104/125) piece1397
    intervalAccepted1397 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1398 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1398 : candidateIntervalCheck candidate1398 (104/125) (8321/10000) piece1398=true := by decide +kernel
noncomputable def cell1398 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1398 accepted1398 (104/125) (8321/10000) piece1398
    intervalAccepted1398 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1399 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1399 : candidateIntervalCheck candidate1399 (8321/10000) (4161/5000) piece1399=true := by decide +kernel
noncomputable def cell1399 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1399 accepted1399 (8321/10000) (4161/5000) piece1399
    intervalAccepted1399 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1400 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1400 : candidateIntervalCheck candidate1400 (4161/5000) (8323/10000) piece1400=true := by decide +kernel
noncomputable def cell1400 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1400 accepted1400 (4161/5000) (8323/10000) piece1400
    intervalAccepted1400 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1401 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1401 : candidateIntervalCheck candidate1401 (8323/10000) (2081/2500) piece1401=true := by decide +kernel
noncomputable def cell1401 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1401 accepted1401 (8323/10000) (2081/2500) piece1401
    intervalAccepted1401 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1402 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1402 : candidateIntervalCheck candidate1402 (2081/2500) (333/400) piece1402=true := by decide +kernel
noncomputable def cell1402 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1402 accepted1402 (2081/2500) (333/400) piece1402
    intervalAccepted1402 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1403 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1403 : candidateIntervalCheck candidate1403 (333/400) (4163/5000) piece1403=true := by decide +kernel
noncomputable def cell1403 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1403 accepted1403 (333/400) (4163/5000) piece1403
    intervalAccepted1403 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1404 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1404 : candidateIntervalCheck candidate1404 (4163/5000) (8327/10000) piece1404=true := by decide +kernel
noncomputable def cell1404 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1404 accepted1404 (4163/5000) (8327/10000) piece1404
    intervalAccepted1404 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1405 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1405 : candidateIntervalCheck candidate1405 (8327/10000) (1041/1250) piece1405=true := by decide +kernel
noncomputable def cell1405 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1405 accepted1405 (8327/10000) (1041/1250) piece1405
    intervalAccepted1405 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1406 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1406 : candidateIntervalCheck candidate1406 (1041/1250) (8329/10000) piece1406=true := by decide +kernel
noncomputable def cell1406 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1406 accepted1406 (1041/1250) (8329/10000) piece1406
    intervalAccepted1406 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1407 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1407 : candidateIntervalCheck candidate1407 (8329/10000) (833/1000) piece1407=true := by decide +kernel
noncomputable def cell1407 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1407 accepted1407 (8329/10000) (833/1000) piece1407
    intervalAccepted1407 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1392, cell1393, cell1394, cell1395, cell1396, cell1397, cell1398, cell1399, cell1400, cell1401, cell1402, cell1403, cell1404, cell1405, cell1406, cell1407]
theorem chainAccepted : spinCellChainCheck (4157/5000) (833/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4157/5000) (833/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0087
