module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0027

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0027
open CandidateBatch0027 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0432 : AffinePiece := pieces[392]'(by decide +kernel)
theorem intervalAccepted0432 : candidateIntervalCheck candidate0432 (1429/10000) (1431/10000) piece0432=true := by decide +kernel
noncomputable def cell0432 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0432 accepted0432 (1429/10000) (1431/10000) piece0432
    intervalAccepted0432 (fun t => piece_le_psi ⟨392,by decide +kernel⟩ t)
def piece0433 : AffinePiece := pieces[393]'(by decide +kernel)
theorem intervalAccepted0433 : candidateIntervalCheck candidate0433 (1431/10000) (1433/10000) piece0433=true := by decide +kernel
noncomputable def cell0433 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0433 accepted0433 (1431/10000) (1433/10000) piece0433
    intervalAccepted0433 (fun t => piece_le_psi ⟨393,by decide +kernel⟩ t)
def piece0434 : AffinePiece := pieces[394]'(by decide +kernel)
theorem intervalAccepted0434 : candidateIntervalCheck candidate0434 (1433/10000) (287/2000) piece0434=true := by decide +kernel
noncomputable def cell0434 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0434 accepted0434 (1433/10000) (287/2000) piece0434
    intervalAccepted0434 (fun t => piece_le_psi ⟨394,by decide +kernel⟩ t)
def piece0435 : AffinePiece := pieces[395]'(by decide +kernel)
theorem intervalAccepted0435 : candidateIntervalCheck candidate0435 (287/2000) (1437/10000) piece0435=true := by decide +kernel
noncomputable def cell0435 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0435 accepted0435 (287/2000) (1437/10000) piece0435
    intervalAccepted0435 (fun t => piece_le_psi ⟨395,by decide +kernel⟩ t)
def piece0436 : AffinePiece := pieces[396]'(by decide +kernel)
theorem intervalAccepted0436 : candidateIntervalCheck candidate0436 (1437/10000) (1439/10000) piece0436=true := by decide +kernel
noncomputable def cell0436 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0436 accepted0436 (1437/10000) (1439/10000) piece0436
    intervalAccepted0436 (fun t => piece_le_psi ⟨396,by decide +kernel⟩ t)
def piece0437 : AffinePiece := pieces[397]'(by decide +kernel)
theorem intervalAccepted0437 : candidateIntervalCheck candidate0437 (1439/10000) (1441/10000) piece0437=true := by decide +kernel
noncomputable def cell0437 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0437 accepted0437 (1439/10000) (1441/10000) piece0437
    intervalAccepted0437 (fun t => piece_le_psi ⟨397,by decide +kernel⟩ t)
def piece0438 : AffinePiece := pieces[398]'(by decide +kernel)
theorem intervalAccepted0438 : candidateIntervalCheck candidate0438 (1441/10000) (1443/10000) piece0438=true := by decide +kernel
noncomputable def cell0438 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0438 accepted0438 (1441/10000) (1443/10000) piece0438
    intervalAccepted0438 (fun t => piece_le_psi ⟨398,by decide +kernel⟩ t)
def piece0439 : AffinePiece := pieces[399]'(by decide +kernel)
theorem intervalAccepted0439 : candidateIntervalCheck candidate0439 (1443/10000) (289/2000) piece0439=true := by decide +kernel
noncomputable def cell0439 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0439 accepted0439 (1443/10000) (289/2000) piece0439
    intervalAccepted0439 (fun t => piece_le_psi ⟨399,by decide +kernel⟩ t)
def piece0440 : AffinePiece := pieces[400]'(by decide +kernel)
theorem intervalAccepted0440 : candidateIntervalCheck candidate0440 (289/2000) (1447/10000) piece0440=true := by decide +kernel
noncomputable def cell0440 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0440 accepted0440 (289/2000) (1447/10000) piece0440
    intervalAccepted0440 (fun t => piece_le_psi ⟨400,by decide +kernel⟩ t)
def piece0441 : AffinePiece := pieces[401]'(by decide +kernel)
theorem intervalAccepted0441 : candidateIntervalCheck candidate0441 (1447/10000) (1449/10000) piece0441=true := by decide +kernel
noncomputable def cell0441 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0441 accepted0441 (1447/10000) (1449/10000) piece0441
    intervalAccepted0441 (fun t => piece_le_psi ⟨401,by decide +kernel⟩ t)
def piece0442 : AffinePiece := pieces[402]'(by decide +kernel)
theorem intervalAccepted0442 : candidateIntervalCheck candidate0442 (1449/10000) (1451/10000) piece0442=true := by decide +kernel
noncomputable def cell0442 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0442 accepted0442 (1449/10000) (1451/10000) piece0442
    intervalAccepted0442 (fun t => piece_le_psi ⟨402,by decide +kernel⟩ t)
def piece0443 : AffinePiece := pieces[403]'(by decide +kernel)
theorem intervalAccepted0443 : candidateIntervalCheck candidate0443 (1451/10000) (1453/10000) piece0443=true := by decide +kernel
noncomputable def cell0443 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0443 accepted0443 (1451/10000) (1453/10000) piece0443
    intervalAccepted0443 (fun t => piece_le_psi ⟨403,by decide +kernel⟩ t)
def piece0444 : AffinePiece := pieces[404]'(by decide +kernel)
theorem intervalAccepted0444 : candidateIntervalCheck candidate0444 (1453/10000) (291/2000) piece0444=true := by decide +kernel
noncomputable def cell0444 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0444 accepted0444 (1453/10000) (291/2000) piece0444
    intervalAccepted0444 (fun t => piece_le_psi ⟨404,by decide +kernel⟩ t)
def piece0445 : AffinePiece := pieces[405]'(by decide +kernel)
theorem intervalAccepted0445 : candidateIntervalCheck candidate0445 (291/2000) (1457/10000) piece0445=true := by decide +kernel
noncomputable def cell0445 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0445 accepted0445 (291/2000) (1457/10000) piece0445
    intervalAccepted0445 (fun t => piece_le_psi ⟨405,by decide +kernel⟩ t)
def piece0446 : AffinePiece := pieces[406]'(by decide +kernel)
theorem intervalAccepted0446 : candidateIntervalCheck candidate0446 (1457/10000) (1459/10000) piece0446=true := by decide +kernel
noncomputable def cell0446 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0446 accepted0446 (1457/10000) (1459/10000) piece0446
    intervalAccepted0446 (fun t => piece_le_psi ⟨406,by decide +kernel⟩ t)
def piece0447 : AffinePiece := pieces[407]'(by decide +kernel)
theorem intervalAccepted0447 : candidateIntervalCheck candidate0447 (1459/10000) (1461/10000) piece0447=true := by decide +kernel
noncomputable def cell0447 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0447 accepted0447 (1459/10000) (1461/10000) piece0447
    intervalAccepted0447 (fun t => piece_le_psi ⟨407,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0432, cell0433, cell0434, cell0435, cell0436, cell0437, cell0438, cell0439, cell0440, cell0441, cell0442, cell0443, cell0444, cell0445, cell0446, cell0447]
theorem chainAccepted : spinCellChainCheck (1429/10000) (1461/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1429/10000) (1461/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0027
