import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0031
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0031
open CandidateBatch0031 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0496 : AffinePiece := pieces[456]'(by decide +kernel)
theorem intervalAccepted0496 : candidateIntervalCheck candidate0496 (1557/10000) (1559/10000) piece0496=true := by decide +kernel
noncomputable def cell0496 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0496 accepted0496 (1557/10000) (1559/10000) piece0496
    intervalAccepted0496 (fun t => piece_le_psi ⟨456,by decide +kernel⟩ t)
def piece0497 : AffinePiece := pieces[457]'(by decide +kernel)
theorem intervalAccepted0497 : candidateIntervalCheck candidate0497 (1559/10000) (1561/10000) piece0497=true := by decide +kernel
noncomputable def cell0497 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0497 accepted0497 (1559/10000) (1561/10000) piece0497
    intervalAccepted0497 (fun t => piece_le_psi ⟨457,by decide +kernel⟩ t)
def piece0498 : AffinePiece := pieces[458]'(by decide +kernel)
theorem intervalAccepted0498 : candidateIntervalCheck candidate0498 (1561/10000) (1563/10000) piece0498=true := by decide +kernel
noncomputable def cell0498 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0498 accepted0498 (1561/10000) (1563/10000) piece0498
    intervalAccepted0498 (fun t => piece_le_psi ⟨458,by decide +kernel⟩ t)
def piece0499 : AffinePiece := pieces[459]'(by decide +kernel)
theorem intervalAccepted0499 : candidateIntervalCheck candidate0499 (1563/10000) (313/2000) piece0499=true := by decide +kernel
noncomputable def cell0499 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0499 accepted0499 (1563/10000) (313/2000) piece0499
    intervalAccepted0499 (fun t => piece_le_psi ⟨459,by decide +kernel⟩ t)
def piece0500 : AffinePiece := pieces[460]'(by decide +kernel)
theorem intervalAccepted0500 : candidateIntervalCheck candidate0500 (313/2000) (1567/10000) piece0500=true := by decide +kernel
noncomputable def cell0500 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0500 accepted0500 (313/2000) (1567/10000) piece0500
    intervalAccepted0500 (fun t => piece_le_psi ⟨460,by decide +kernel⟩ t)
def piece0501 : AffinePiece := pieces[461]'(by decide +kernel)
theorem intervalAccepted0501 : candidateIntervalCheck candidate0501 (1567/10000) (1569/10000) piece0501=true := by decide +kernel
noncomputable def cell0501 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0501 accepted0501 (1567/10000) (1569/10000) piece0501
    intervalAccepted0501 (fun t => piece_le_psi ⟨461,by decide +kernel⟩ t)
def piece0502 : AffinePiece := pieces[462]'(by decide +kernel)
theorem intervalAccepted0502 : candidateIntervalCheck candidate0502 (1569/10000) (1571/10000) piece0502=true := by decide +kernel
noncomputable def cell0502 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0502 accepted0502 (1569/10000) (1571/10000) piece0502
    intervalAccepted0502 (fun t => piece_le_psi ⟨462,by decide +kernel⟩ t)
def piece0503 : AffinePiece := pieces[463]'(by decide +kernel)
theorem intervalAccepted0503 : candidateIntervalCheck candidate0503 (1571/10000) (1573/10000) piece0503=true := by decide +kernel
noncomputable def cell0503 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0503 accepted0503 (1571/10000) (1573/10000) piece0503
    intervalAccepted0503 (fun t => piece_le_psi ⟨463,by decide +kernel⟩ t)
def piece0504 : AffinePiece := pieces[464]'(by decide +kernel)
theorem intervalAccepted0504 : candidateIntervalCheck candidate0504 (1573/10000) (63/400) piece0504=true := by decide +kernel
noncomputable def cell0504 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0504 accepted0504 (1573/10000) (63/400) piece0504
    intervalAccepted0504 (fun t => piece_le_psi ⟨464,by decide +kernel⟩ t)
def piece0505 : AffinePiece := pieces[465]'(by decide +kernel)
theorem intervalAccepted0505 : candidateIntervalCheck candidate0505 (63/400) (1577/10000) piece0505=true := by decide +kernel
noncomputable def cell0505 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0505 accepted0505 (63/400) (1577/10000) piece0505
    intervalAccepted0505 (fun t => piece_le_psi ⟨465,by decide +kernel⟩ t)
def piece0506 : AffinePiece := pieces[466]'(by decide +kernel)
theorem intervalAccepted0506 : candidateIntervalCheck candidate0506 (1577/10000) (1579/10000) piece0506=true := by decide +kernel
noncomputable def cell0506 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0506 accepted0506 (1577/10000) (1579/10000) piece0506
    intervalAccepted0506 (fun t => piece_le_psi ⟨466,by decide +kernel⟩ t)
def piece0507 : AffinePiece := pieces[467]'(by decide +kernel)
theorem intervalAccepted0507 : candidateIntervalCheck candidate0507 (1579/10000) (1581/10000) piece0507=true := by decide +kernel
noncomputable def cell0507 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0507 accepted0507 (1579/10000) (1581/10000) piece0507
    intervalAccepted0507 (fun t => piece_le_psi ⟨467,by decide +kernel⟩ t)
def piece0508 : AffinePiece := pieces[468]'(by decide +kernel)
theorem intervalAccepted0508 : candidateIntervalCheck candidate0508 (1581/10000) (1583/10000) piece0508=true := by decide +kernel
noncomputable def cell0508 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0508 accepted0508 (1581/10000) (1583/10000) piece0508
    intervalAccepted0508 (fun t => piece_le_psi ⟨468,by decide +kernel⟩ t)
def piece0509 : AffinePiece := pieces[469]'(by decide +kernel)
theorem intervalAccepted0509 : candidateIntervalCheck candidate0509 (1583/10000) (317/2000) piece0509=true := by decide +kernel
noncomputable def cell0509 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0509 accepted0509 (1583/10000) (317/2000) piece0509
    intervalAccepted0509 (fun t => piece_le_psi ⟨469,by decide +kernel⟩ t)
def piece0510 : AffinePiece := pieces[470]'(by decide +kernel)
theorem intervalAccepted0510 : candidateIntervalCheck candidate0510 (317/2000) (1587/10000) piece0510=true := by decide +kernel
noncomputable def cell0510 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0510 accepted0510 (317/2000) (1587/10000) piece0510
    intervalAccepted0510 (fun t => piece_le_psi ⟨470,by decide +kernel⟩ t)
def piece0511 : AffinePiece := pieces[471]'(by decide +kernel)
theorem intervalAccepted0511 : candidateIntervalCheck candidate0511 (1587/10000) (1589/10000) piece0511=true := by decide +kernel
noncomputable def cell0511 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0511 accepted0511 (1587/10000) (1589/10000) piece0511
    intervalAccepted0511 (fun t => piece_le_psi ⟨471,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0496, cell0497, cell0498, cell0499, cell0500, cell0501, cell0502, cell0503, cell0504, cell0505, cell0506, cell0507, cell0508, cell0509, cell0510, cell0511]
theorem chainAccepted : spinCellChainCheck (1557/10000) (1589/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1557/10000) (1589/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0031
