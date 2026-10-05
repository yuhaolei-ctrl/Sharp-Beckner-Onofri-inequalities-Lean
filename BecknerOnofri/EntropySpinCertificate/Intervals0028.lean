module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0028

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0028
open CandidateBatch0028 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0448 : AffinePiece := pieces[408]'(by decide +kernel)
theorem intervalAccepted0448 : candidateIntervalCheck candidate0448 (1461/10000) (1463/10000) piece0448=true := by decide +kernel
noncomputable def cell0448 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0448 accepted0448 (1461/10000) (1463/10000) piece0448
    intervalAccepted0448 (fun t => piece_le_psi ⟨408,by decide +kernel⟩ t)
def piece0449 : AffinePiece := pieces[409]'(by decide +kernel)
theorem intervalAccepted0449 : candidateIntervalCheck candidate0449 (1463/10000) (293/2000) piece0449=true := by decide +kernel
noncomputable def cell0449 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0449 accepted0449 (1463/10000) (293/2000) piece0449
    intervalAccepted0449 (fun t => piece_le_psi ⟨409,by decide +kernel⟩ t)
def piece0450 : AffinePiece := pieces[410]'(by decide +kernel)
theorem intervalAccepted0450 : candidateIntervalCheck candidate0450 (293/2000) (1467/10000) piece0450=true := by decide +kernel
noncomputable def cell0450 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0450 accepted0450 (293/2000) (1467/10000) piece0450
    intervalAccepted0450 (fun t => piece_le_psi ⟨410,by decide +kernel⟩ t)
def piece0451 : AffinePiece := pieces[411]'(by decide +kernel)
theorem intervalAccepted0451 : candidateIntervalCheck candidate0451 (1467/10000) (1469/10000) piece0451=true := by decide +kernel
noncomputable def cell0451 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0451 accepted0451 (1467/10000) (1469/10000) piece0451
    intervalAccepted0451 (fun t => piece_le_psi ⟨411,by decide +kernel⟩ t)
def piece0452 : AffinePiece := pieces[412]'(by decide +kernel)
theorem intervalAccepted0452 : candidateIntervalCheck candidate0452 (1469/10000) (1471/10000) piece0452=true := by decide +kernel
noncomputable def cell0452 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0452 accepted0452 (1469/10000) (1471/10000) piece0452
    intervalAccepted0452 (fun t => piece_le_psi ⟨412,by decide +kernel⟩ t)
def piece0453 : AffinePiece := pieces[413]'(by decide +kernel)
theorem intervalAccepted0453 : candidateIntervalCheck candidate0453 (1471/10000) (1473/10000) piece0453=true := by decide +kernel
noncomputable def cell0453 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0453 accepted0453 (1471/10000) (1473/10000) piece0453
    intervalAccepted0453 (fun t => piece_le_psi ⟨413,by decide +kernel⟩ t)
def piece0454 : AffinePiece := pieces[414]'(by decide +kernel)
theorem intervalAccepted0454 : candidateIntervalCheck candidate0454 (1473/10000) (59/400) piece0454=true := by decide +kernel
noncomputable def cell0454 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0454 accepted0454 (1473/10000) (59/400) piece0454
    intervalAccepted0454 (fun t => piece_le_psi ⟨414,by decide +kernel⟩ t)
def piece0455 : AffinePiece := pieces[415]'(by decide +kernel)
theorem intervalAccepted0455 : candidateIntervalCheck candidate0455 (59/400) (1477/10000) piece0455=true := by decide +kernel
noncomputable def cell0455 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0455 accepted0455 (59/400) (1477/10000) piece0455
    intervalAccepted0455 (fun t => piece_le_psi ⟨415,by decide +kernel⟩ t)
def piece0456 : AffinePiece := pieces[416]'(by decide +kernel)
theorem intervalAccepted0456 : candidateIntervalCheck candidate0456 (1477/10000) (1479/10000) piece0456=true := by decide +kernel
noncomputable def cell0456 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0456 accepted0456 (1477/10000) (1479/10000) piece0456
    intervalAccepted0456 (fun t => piece_le_psi ⟨416,by decide +kernel⟩ t)
def piece0457 : AffinePiece := pieces[417]'(by decide +kernel)
theorem intervalAccepted0457 : candidateIntervalCheck candidate0457 (1479/10000) (1481/10000) piece0457=true := by decide +kernel
noncomputable def cell0457 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0457 accepted0457 (1479/10000) (1481/10000) piece0457
    intervalAccepted0457 (fun t => piece_le_psi ⟨417,by decide +kernel⟩ t)
def piece0458 : AffinePiece := pieces[418]'(by decide +kernel)
theorem intervalAccepted0458 : candidateIntervalCheck candidate0458 (1481/10000) (1483/10000) piece0458=true := by decide +kernel
noncomputable def cell0458 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0458 accepted0458 (1481/10000) (1483/10000) piece0458
    intervalAccepted0458 (fun t => piece_le_psi ⟨418,by decide +kernel⟩ t)
def piece0459 : AffinePiece := pieces[419]'(by decide +kernel)
theorem intervalAccepted0459 : candidateIntervalCheck candidate0459 (1483/10000) (297/2000) piece0459=true := by decide +kernel
noncomputable def cell0459 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0459 accepted0459 (1483/10000) (297/2000) piece0459
    intervalAccepted0459 (fun t => piece_le_psi ⟨419,by decide +kernel⟩ t)
def piece0460 : AffinePiece := pieces[420]'(by decide +kernel)
theorem intervalAccepted0460 : candidateIntervalCheck candidate0460 (297/2000) (1487/10000) piece0460=true := by decide +kernel
noncomputable def cell0460 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0460 accepted0460 (297/2000) (1487/10000) piece0460
    intervalAccepted0460 (fun t => piece_le_psi ⟨420,by decide +kernel⟩ t)
def piece0461 : AffinePiece := pieces[421]'(by decide +kernel)
theorem intervalAccepted0461 : candidateIntervalCheck candidate0461 (1487/10000) (1489/10000) piece0461=true := by decide +kernel
noncomputable def cell0461 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0461 accepted0461 (1487/10000) (1489/10000) piece0461
    intervalAccepted0461 (fun t => piece_le_psi ⟨421,by decide +kernel⟩ t)
def piece0462 : AffinePiece := pieces[422]'(by decide +kernel)
theorem intervalAccepted0462 : candidateIntervalCheck candidate0462 (1489/10000) (1491/10000) piece0462=true := by decide +kernel
noncomputable def cell0462 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0462 accepted0462 (1489/10000) (1491/10000) piece0462
    intervalAccepted0462 (fun t => piece_le_psi ⟨422,by decide +kernel⟩ t)
def piece0463 : AffinePiece := pieces[423]'(by decide +kernel)
theorem intervalAccepted0463 : candidateIntervalCheck candidate0463 (1491/10000) (1493/10000) piece0463=true := by decide +kernel
noncomputable def cell0463 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0463 accepted0463 (1491/10000) (1493/10000) piece0463
    intervalAccepted0463 (fun t => piece_le_psi ⟨423,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0448, cell0449, cell0450, cell0451, cell0452, cell0453, cell0454, cell0455, cell0456, cell0457, cell0458, cell0459, cell0460, cell0461, cell0462, cell0463]
theorem chainAccepted : spinCellChainCheck (1461/10000) (1493/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1461/10000) (1493/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0028
