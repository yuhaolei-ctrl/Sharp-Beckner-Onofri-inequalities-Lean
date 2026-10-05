module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0092

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0092
open CandidateBatch0092 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1472 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1472 : candidateIntervalCheck candidate1472 (4197/5000) (1679/2000) piece1472=true := by decide +kernel
noncomputable def cell1472 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1472 accepted1472 (4197/5000) (1679/2000) piece1472
    intervalAccepted1472 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1473 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1473 : candidateIntervalCheck candidate1473 (1679/2000) (2099/2500) piece1473=true := by decide +kernel
noncomputable def cell1473 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1473 accepted1473 (1679/2000) (2099/2500) piece1473
    intervalAccepted1473 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1474 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1474 : candidateIntervalCheck candidate1474 (2099/2500) (8397/10000) piece1474=true := by decide +kernel
noncomputable def cell1474 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1474 accepted1474 (2099/2500) (8397/10000) piece1474
    intervalAccepted1474 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1475 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1475 : candidateIntervalCheck candidate1475 (8397/10000) (4199/5000) piece1475=true := by decide +kernel
noncomputable def cell1475 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1475 accepted1475 (8397/10000) (4199/5000) piece1475
    intervalAccepted1475 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1476 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1476 : candidateIntervalCheck candidate1476 (4199/5000) (8399/10000) piece1476=true := by decide +kernel
noncomputable def cell1476 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1476 accepted1476 (4199/5000) (8399/10000) piece1476
    intervalAccepted1476 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1477 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1477 : candidateIntervalCheck candidate1477 (8399/10000) (21/25) piece1477=true := by decide +kernel
noncomputable def cell1477 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1477 accepted1477 (8399/10000) (21/25) piece1477
    intervalAccepted1477 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1478 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1478 : candidateIntervalCheck candidate1478 (21/25) (8401/10000) piece1478=true := by decide +kernel
noncomputable def cell1478 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1478 accepted1478 (21/25) (8401/10000) piece1478
    intervalAccepted1478 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1479 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1479 : candidateIntervalCheck candidate1479 (8401/10000) (4201/5000) piece1479=true := by decide +kernel
noncomputable def cell1479 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1479 accepted1479 (8401/10000) (4201/5000) piece1479
    intervalAccepted1479 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1480 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1480 : candidateIntervalCheck candidate1480 (4201/5000) (8403/10000) piece1480=true := by decide +kernel
noncomputable def cell1480 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1480 accepted1480 (4201/5000) (8403/10000) piece1480
    intervalAccepted1480 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1481 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1481 : candidateIntervalCheck candidate1481 (8403/10000) (2101/2500) piece1481=true := by decide +kernel
noncomputable def cell1481 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1481 accepted1481 (8403/10000) (2101/2500) piece1481
    intervalAccepted1481 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1482 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1482 : candidateIntervalCheck candidate1482 (2101/2500) (1681/2000) piece1482=true := by decide +kernel
noncomputable def cell1482 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1482 accepted1482 (2101/2500) (1681/2000) piece1482
    intervalAccepted1482 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1483 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1483 : candidateIntervalCheck candidate1483 (1681/2000) (4203/5000) piece1483=true := by decide +kernel
noncomputable def cell1483 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1483 accepted1483 (1681/2000) (4203/5000) piece1483
    intervalAccepted1483 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1484 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1484 : candidateIntervalCheck candidate1484 (4203/5000) (8407/10000) piece1484=true := by decide +kernel
noncomputable def cell1484 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1484 accepted1484 (4203/5000) (8407/10000) piece1484
    intervalAccepted1484 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1485 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1485 : candidateIntervalCheck candidate1485 (8407/10000) (1051/1250) piece1485=true := by decide +kernel
noncomputable def cell1485 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1485 accepted1485 (8407/10000) (1051/1250) piece1485
    intervalAccepted1485 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1486 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1486 : candidateIntervalCheck candidate1486 (1051/1250) (8409/10000) piece1486=true := by decide +kernel
noncomputable def cell1486 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1486 accepted1486 (1051/1250) (8409/10000) piece1486
    intervalAccepted1486 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1487 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1487 : candidateIntervalCheck candidate1487 (8409/10000) (841/1000) piece1487=true := by decide +kernel
noncomputable def cell1487 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1487 accepted1487 (8409/10000) (841/1000) piece1487
    intervalAccepted1487 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1472, cell1473, cell1474, cell1475, cell1476, cell1477, cell1478, cell1479, cell1480, cell1481, cell1482, cell1483, cell1484, cell1485, cell1486, cell1487]
theorem chainAccepted : spinCellChainCheck (4197/5000) (841/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4197/5000) (841/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0092
