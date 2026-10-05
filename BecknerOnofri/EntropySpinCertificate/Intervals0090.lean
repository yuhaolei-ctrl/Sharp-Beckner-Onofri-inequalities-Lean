module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0090

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0090
open CandidateBatch0090 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1440 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1440 : candidateIntervalCheck candidate1440 (4181/5000) (8363/10000) piece1440=true := by decide +kernel
noncomputable def cell1440 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1440 accepted1440 (4181/5000) (8363/10000) piece1440
    intervalAccepted1440 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1441 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1441 : candidateIntervalCheck candidate1441 (8363/10000) (2091/2500) piece1441=true := by decide +kernel
noncomputable def cell1441 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1441 accepted1441 (8363/10000) (2091/2500) piece1441
    intervalAccepted1441 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1442 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1442 : candidateIntervalCheck candidate1442 (2091/2500) (1673/2000) piece1442=true := by decide +kernel
noncomputable def cell1442 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1442 accepted1442 (2091/2500) (1673/2000) piece1442
    intervalAccepted1442 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1443 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1443 : candidateIntervalCheck candidate1443 (1673/2000) (4183/5000) piece1443=true := by decide +kernel
noncomputable def cell1443 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1443 accepted1443 (1673/2000) (4183/5000) piece1443
    intervalAccepted1443 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1444 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1444 : candidateIntervalCheck candidate1444 (4183/5000) (8367/10000) piece1444=true := by decide +kernel
noncomputable def cell1444 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1444 accepted1444 (4183/5000) (8367/10000) piece1444
    intervalAccepted1444 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1445 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1445 : candidateIntervalCheck candidate1445 (8367/10000) (523/625) piece1445=true := by decide +kernel
noncomputable def cell1445 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1445 accepted1445 (8367/10000) (523/625) piece1445
    intervalAccepted1445 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1446 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1446 : candidateIntervalCheck candidate1446 (523/625) (8369/10000) piece1446=true := by decide +kernel
noncomputable def cell1446 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1446 accepted1446 (523/625) (8369/10000) piece1446
    intervalAccepted1446 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1447 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1447 : candidateIntervalCheck candidate1447 (8369/10000) (837/1000) piece1447=true := by decide +kernel
noncomputable def cell1447 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1447 accepted1447 (8369/10000) (837/1000) piece1447
    intervalAccepted1447 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1448 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1448 : candidateIntervalCheck candidate1448 (837/1000) (8371/10000) piece1448=true := by decide +kernel
noncomputable def cell1448 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1448 accepted1448 (837/1000) (8371/10000) piece1448
    intervalAccepted1448 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1449 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1449 : candidateIntervalCheck candidate1449 (8371/10000) (2093/2500) piece1449=true := by decide +kernel
noncomputable def cell1449 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1449 accepted1449 (8371/10000) (2093/2500) piece1449
    intervalAccepted1449 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1450 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1450 : candidateIntervalCheck candidate1450 (2093/2500) (8373/10000) piece1450=true := by decide +kernel
noncomputable def cell1450 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1450 accepted1450 (2093/2500) (8373/10000) piece1450
    intervalAccepted1450 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1451 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1451 : candidateIntervalCheck candidate1451 (8373/10000) (4187/5000) piece1451=true := by decide +kernel
noncomputable def cell1451 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1451 accepted1451 (8373/10000) (4187/5000) piece1451
    intervalAccepted1451 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1452 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1452 : candidateIntervalCheck candidate1452 (4187/5000) (67/80) piece1452=true := by decide +kernel
noncomputable def cell1452 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1452 accepted1452 (4187/5000) (67/80) piece1452
    intervalAccepted1452 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1453 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1453 : candidateIntervalCheck candidate1453 (67/80) (1047/1250) piece1453=true := by decide +kernel
noncomputable def cell1453 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1453 accepted1453 (67/80) (1047/1250) piece1453
    intervalAccepted1453 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1454 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1454 : candidateIntervalCheck candidate1454 (1047/1250) (8377/10000) piece1454=true := by decide +kernel
noncomputable def cell1454 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1454 accepted1454 (1047/1250) (8377/10000) piece1454
    intervalAccepted1454 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1455 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1455 : candidateIntervalCheck candidate1455 (8377/10000) (4189/5000) piece1455=true := by decide +kernel
noncomputable def cell1455 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1455 accepted1455 (8377/10000) (4189/5000) piece1455
    intervalAccepted1455 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1440, cell1441, cell1442, cell1443, cell1444, cell1445, cell1446, cell1447, cell1448, cell1449, cell1450, cell1451, cell1452, cell1453, cell1454, cell1455]
theorem chainAccepted : spinCellChainCheck (4181/5000) (4189/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4181/5000) (4189/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0090
