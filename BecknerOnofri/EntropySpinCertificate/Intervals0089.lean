module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0089

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0089
open CandidateBatch0089 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1424 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1424 : candidateIntervalCheck candidate1424 (4173/5000) (8347/10000) piece1424=true := by decide +kernel
noncomputable def cell1424 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1424 accepted1424 (4173/5000) (8347/10000) piece1424
    intervalAccepted1424 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1425 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1425 : candidateIntervalCheck candidate1425 (8347/10000) (2087/2500) piece1425=true := by decide +kernel
noncomputable def cell1425 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1425 accepted1425 (8347/10000) (2087/2500) piece1425
    intervalAccepted1425 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1426 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1426 : candidateIntervalCheck candidate1426 (2087/2500) (8349/10000) piece1426=true := by decide +kernel
noncomputable def cell1426 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1426 accepted1426 (2087/2500) (8349/10000) piece1426
    intervalAccepted1426 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1427 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1427 : candidateIntervalCheck candidate1427 (8349/10000) (167/200) piece1427=true := by decide +kernel
noncomputable def cell1427 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1427 accepted1427 (8349/10000) (167/200) piece1427
    intervalAccepted1427 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1428 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1428 : candidateIntervalCheck candidate1428 (167/200) (8351/10000) piece1428=true := by decide +kernel
noncomputable def cell1428 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1428 accepted1428 (167/200) (8351/10000) piece1428
    intervalAccepted1428 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1429 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1429 : candidateIntervalCheck candidate1429 (8351/10000) (522/625) piece1429=true := by decide +kernel
noncomputable def cell1429 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1429 accepted1429 (8351/10000) (522/625) piece1429
    intervalAccepted1429 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1430 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1430 : candidateIntervalCheck candidate1430 (522/625) (8353/10000) piece1430=true := by decide +kernel
noncomputable def cell1430 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1430 accepted1430 (522/625) (8353/10000) piece1430
    intervalAccepted1430 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1431 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1431 : candidateIntervalCheck candidate1431 (8353/10000) (4177/5000) piece1431=true := by decide +kernel
noncomputable def cell1431 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1431 accepted1431 (8353/10000) (4177/5000) piece1431
    intervalAccepted1431 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1432 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1432 : candidateIntervalCheck candidate1432 (4177/5000) (1671/2000) piece1432=true := by decide +kernel
noncomputable def cell1432 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1432 accepted1432 (4177/5000) (1671/2000) piece1432
    intervalAccepted1432 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1433 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1433 : candidateIntervalCheck candidate1433 (1671/2000) (2089/2500) piece1433=true := by decide +kernel
noncomputable def cell1433 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1433 accepted1433 (1671/2000) (2089/2500) piece1433
    intervalAccepted1433 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1434 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1434 : candidateIntervalCheck candidate1434 (2089/2500) (8357/10000) piece1434=true := by decide +kernel
noncomputable def cell1434 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1434 accepted1434 (2089/2500) (8357/10000) piece1434
    intervalAccepted1434 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1435 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1435 : candidateIntervalCheck candidate1435 (8357/10000) (4179/5000) piece1435=true := by decide +kernel
noncomputable def cell1435 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1435 accepted1435 (8357/10000) (4179/5000) piece1435
    intervalAccepted1435 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1436 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1436 : candidateIntervalCheck candidate1436 (4179/5000) (8359/10000) piece1436=true := by decide +kernel
noncomputable def cell1436 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1436 accepted1436 (4179/5000) (8359/10000) piece1436
    intervalAccepted1436 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1437 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1437 : candidateIntervalCheck candidate1437 (8359/10000) (209/250) piece1437=true := by decide +kernel
noncomputable def cell1437 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1437 accepted1437 (8359/10000) (209/250) piece1437
    intervalAccepted1437 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1438 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1438 : candidateIntervalCheck candidate1438 (209/250) (8361/10000) piece1438=true := by decide +kernel
noncomputable def cell1438 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1438 accepted1438 (209/250) (8361/10000) piece1438
    intervalAccepted1438 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1439 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1439 : candidateIntervalCheck candidate1439 (8361/10000) (4181/5000) piece1439=true := by decide +kernel
noncomputable def cell1439 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1439 accepted1439 (8361/10000) (4181/5000) piece1439
    intervalAccepted1439 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1424, cell1425, cell1426, cell1427, cell1428, cell1429, cell1430, cell1431, cell1432, cell1433, cell1434, cell1435, cell1436, cell1437, cell1438, cell1439]
theorem chainAccepted : spinCellChainCheck (4173/5000) (4181/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4173/5000) (4181/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0089
