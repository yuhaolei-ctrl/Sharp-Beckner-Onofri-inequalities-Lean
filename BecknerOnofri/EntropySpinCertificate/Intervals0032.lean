import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0032
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0032
open CandidateBatch0032 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0512 : AffinePiece := pieces[472]'(by decide +kernel)
theorem intervalAccepted0512 : candidateIntervalCheck candidate0512 (1589/10000) (1591/10000) piece0512=true := by decide +kernel
noncomputable def cell0512 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0512 accepted0512 (1589/10000) (1591/10000) piece0512
    intervalAccepted0512 (fun t => piece_le_psi ⟨472,by decide +kernel⟩ t)
def piece0513 : AffinePiece := pieces[473]'(by decide +kernel)
theorem intervalAccepted0513 : candidateIntervalCheck candidate0513 (1591/10000) (1593/10000) piece0513=true := by decide +kernel
noncomputable def cell0513 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0513 accepted0513 (1591/10000) (1593/10000) piece0513
    intervalAccepted0513 (fun t => piece_le_psi ⟨473,by decide +kernel⟩ t)
def piece0514 : AffinePiece := pieces[474]'(by decide +kernel)
theorem intervalAccepted0514 : candidateIntervalCheck candidate0514 (1593/10000) (319/2000) piece0514=true := by decide +kernel
noncomputable def cell0514 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0514 accepted0514 (1593/10000) (319/2000) piece0514
    intervalAccepted0514 (fun t => piece_le_psi ⟨474,by decide +kernel⟩ t)
def piece0515 : AffinePiece := pieces[475]'(by decide +kernel)
theorem intervalAccepted0515 : candidateIntervalCheck candidate0515 (319/2000) (1597/10000) piece0515=true := by decide +kernel
noncomputable def cell0515 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0515 accepted0515 (319/2000) (1597/10000) piece0515
    intervalAccepted0515 (fun t => piece_le_psi ⟨475,by decide +kernel⟩ t)
def piece0516 : AffinePiece := pieces[476]'(by decide +kernel)
theorem intervalAccepted0516 : candidateIntervalCheck candidate0516 (1597/10000) (1599/10000) piece0516=true := by decide +kernel
noncomputable def cell0516 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0516 accepted0516 (1597/10000) (1599/10000) piece0516
    intervalAccepted0516 (fun t => piece_le_psi ⟨476,by decide +kernel⟩ t)
def piece0517 : AffinePiece := pieces[477]'(by decide +kernel)
theorem intervalAccepted0517 : candidateIntervalCheck candidate0517 (1599/10000) (1601/10000) piece0517=true := by decide +kernel
noncomputable def cell0517 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0517 accepted0517 (1599/10000) (1601/10000) piece0517
    intervalAccepted0517 (fun t => piece_le_psi ⟨477,by decide +kernel⟩ t)
def piece0518 : AffinePiece := pieces[478]'(by decide +kernel)
theorem intervalAccepted0518 : candidateIntervalCheck candidate0518 (1601/10000) (1603/10000) piece0518=true := by decide +kernel
noncomputable def cell0518 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0518 accepted0518 (1601/10000) (1603/10000) piece0518
    intervalAccepted0518 (fun t => piece_le_psi ⟨478,by decide +kernel⟩ t)
def piece0519 : AffinePiece := pieces[479]'(by decide +kernel)
theorem intervalAccepted0519 : candidateIntervalCheck candidate0519 (1603/10000) (321/2000) piece0519=true := by decide +kernel
noncomputable def cell0519 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0519 accepted0519 (1603/10000) (321/2000) piece0519
    intervalAccepted0519 (fun t => piece_le_psi ⟨479,by decide +kernel⟩ t)
def piece0520 : AffinePiece := pieces[480]'(by decide +kernel)
theorem intervalAccepted0520 : candidateIntervalCheck candidate0520 (321/2000) (1607/10000) piece0520=true := by decide +kernel
noncomputable def cell0520 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0520 accepted0520 (321/2000) (1607/10000) piece0520
    intervalAccepted0520 (fun t => piece_le_psi ⟨480,by decide +kernel⟩ t)
def piece0521 : AffinePiece := pieces[481]'(by decide +kernel)
theorem intervalAccepted0521 : candidateIntervalCheck candidate0521 (1607/10000) (1609/10000) piece0521=true := by decide +kernel
noncomputable def cell0521 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0521 accepted0521 (1607/10000) (1609/10000) piece0521
    intervalAccepted0521 (fun t => piece_le_psi ⟨481,by decide +kernel⟩ t)
def piece0522 : AffinePiece := pieces[482]'(by decide +kernel)
theorem intervalAccepted0522 : candidateIntervalCheck candidate0522 (1609/10000) (1611/10000) piece0522=true := by decide +kernel
noncomputable def cell0522 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0522 accepted0522 (1609/10000) (1611/10000) piece0522
    intervalAccepted0522 (fun t => piece_le_psi ⟨482,by decide +kernel⟩ t)
def piece0523 : AffinePiece := pieces[483]'(by decide +kernel)
theorem intervalAccepted0523 : candidateIntervalCheck candidate0523 (1611/10000) (1613/10000) piece0523=true := by decide +kernel
noncomputable def cell0523 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0523 accepted0523 (1611/10000) (1613/10000) piece0523
    intervalAccepted0523 (fun t => piece_le_psi ⟨483,by decide +kernel⟩ t)
def piece0524 : AffinePiece := pieces[484]'(by decide +kernel)
theorem intervalAccepted0524 : candidateIntervalCheck candidate0524 (1613/10000) (323/2000) piece0524=true := by decide +kernel
noncomputable def cell0524 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0524 accepted0524 (1613/10000) (323/2000) piece0524
    intervalAccepted0524 (fun t => piece_le_psi ⟨484,by decide +kernel⟩ t)
def piece0525 : AffinePiece := pieces[485]'(by decide +kernel)
theorem intervalAccepted0525 : candidateIntervalCheck candidate0525 (323/2000) (1617/10000) piece0525=true := by decide +kernel
noncomputable def cell0525 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0525 accepted0525 (323/2000) (1617/10000) piece0525
    intervalAccepted0525 (fun t => piece_le_psi ⟨485,by decide +kernel⟩ t)
def piece0526 : AffinePiece := pieces[486]'(by decide +kernel)
theorem intervalAccepted0526 : candidateIntervalCheck candidate0526 (1617/10000) (1619/10000) piece0526=true := by decide +kernel
noncomputable def cell0526 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0526 accepted0526 (1617/10000) (1619/10000) piece0526
    intervalAccepted0526 (fun t => piece_le_psi ⟨486,by decide +kernel⟩ t)
def piece0527 : AffinePiece := pieces[487]'(by decide +kernel)
theorem intervalAccepted0527 : candidateIntervalCheck candidate0527 (1619/10000) (1621/10000) piece0527=true := by decide +kernel
noncomputable def cell0527 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0527 accepted0527 (1619/10000) (1621/10000) piece0527
    intervalAccepted0527 (fun t => piece_le_psi ⟨487,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0512, cell0513, cell0514, cell0515, cell0516, cell0517, cell0518, cell0519, cell0520, cell0521, cell0522, cell0523, cell0524, cell0525, cell0526, cell0527]
theorem chainAccepted : spinCellChainCheck (1589/10000) (1621/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1589/10000) (1621/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0032
