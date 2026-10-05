module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0033

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0033
open CandidateBatch0033 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0528 : AffinePiece := pieces[488]'(by decide +kernel)
theorem intervalAccepted0528 : candidateIntervalCheck candidate0528 (1621/10000) (1623/10000) piece0528=true := by decide +kernel
noncomputable def cell0528 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0528 accepted0528 (1621/10000) (1623/10000) piece0528
    intervalAccepted0528 (fun t => piece_le_psi ⟨488,by decide +kernel⟩ t)
def piece0529 : AffinePiece := pieces[489]'(by decide +kernel)
theorem intervalAccepted0529 : candidateIntervalCheck candidate0529 (1623/10000) (13/80) piece0529=true := by decide +kernel
noncomputable def cell0529 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0529 accepted0529 (1623/10000) (13/80) piece0529
    intervalAccepted0529 (fun t => piece_le_psi ⟨489,by decide +kernel⟩ t)
def piece0530 : AffinePiece := pieces[490]'(by decide +kernel)
theorem intervalAccepted0530 : candidateIntervalCheck candidate0530 (13/80) (1627/10000) piece0530=true := by decide +kernel
noncomputable def cell0530 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0530 accepted0530 (13/80) (1627/10000) piece0530
    intervalAccepted0530 (fun t => piece_le_psi ⟨490,by decide +kernel⟩ t)
def piece0531 : AffinePiece := pieces[491]'(by decide +kernel)
theorem intervalAccepted0531 : candidateIntervalCheck candidate0531 (1627/10000) (1629/10000) piece0531=true := by decide +kernel
noncomputable def cell0531 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0531 accepted0531 (1627/10000) (1629/10000) piece0531
    intervalAccepted0531 (fun t => piece_le_psi ⟨491,by decide +kernel⟩ t)
def piece0532 : AffinePiece := pieces[492]'(by decide +kernel)
theorem intervalAccepted0532 : candidateIntervalCheck candidate0532 (1629/10000) (1631/10000) piece0532=true := by decide +kernel
noncomputable def cell0532 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0532 accepted0532 (1629/10000) (1631/10000) piece0532
    intervalAccepted0532 (fun t => piece_le_psi ⟨492,by decide +kernel⟩ t)
def piece0533 : AffinePiece := pieces[493]'(by decide +kernel)
theorem intervalAccepted0533 : candidateIntervalCheck candidate0533 (1631/10000) (1633/10000) piece0533=true := by decide +kernel
noncomputable def cell0533 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0533 accepted0533 (1631/10000) (1633/10000) piece0533
    intervalAccepted0533 (fun t => piece_le_psi ⟨493,by decide +kernel⟩ t)
def piece0534 : AffinePiece := pieces[494]'(by decide +kernel)
theorem intervalAccepted0534 : candidateIntervalCheck candidate0534 (1633/10000) (327/2000) piece0534=true := by decide +kernel
noncomputable def cell0534 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0534 accepted0534 (1633/10000) (327/2000) piece0534
    intervalAccepted0534 (fun t => piece_le_psi ⟨494,by decide +kernel⟩ t)
def piece0535 : AffinePiece := pieces[495]'(by decide +kernel)
theorem intervalAccepted0535 : candidateIntervalCheck candidate0535 (327/2000) (1637/10000) piece0535=true := by decide +kernel
noncomputable def cell0535 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0535 accepted0535 (327/2000) (1637/10000) piece0535
    intervalAccepted0535 (fun t => piece_le_psi ⟨495,by decide +kernel⟩ t)
def piece0536 : AffinePiece := pieces[496]'(by decide +kernel)
theorem intervalAccepted0536 : candidateIntervalCheck candidate0536 (1637/10000) (1639/10000) piece0536=true := by decide +kernel
noncomputable def cell0536 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0536 accepted0536 (1637/10000) (1639/10000) piece0536
    intervalAccepted0536 (fun t => piece_le_psi ⟨496,by decide +kernel⟩ t)
def piece0537 : AffinePiece := pieces[497]'(by decide +kernel)
theorem intervalAccepted0537 : candidateIntervalCheck candidate0537 (1639/10000) (1641/10000) piece0537=true := by decide +kernel
noncomputable def cell0537 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0537 accepted0537 (1639/10000) (1641/10000) piece0537
    intervalAccepted0537 (fun t => piece_le_psi ⟨497,by decide +kernel⟩ t)
def piece0538 : AffinePiece := pieces[498]'(by decide +kernel)
theorem intervalAccepted0538 : candidateIntervalCheck candidate0538 (1641/10000) (1643/10000) piece0538=true := by decide +kernel
noncomputable def cell0538 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0538 accepted0538 (1641/10000) (1643/10000) piece0538
    intervalAccepted0538 (fun t => piece_le_psi ⟨498,by decide +kernel⟩ t)
def piece0539 : AffinePiece := pieces[499]'(by decide +kernel)
theorem intervalAccepted0539 : candidateIntervalCheck candidate0539 (1643/10000) (329/2000) piece0539=true := by decide +kernel
noncomputable def cell0539 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0539 accepted0539 (1643/10000) (329/2000) piece0539
    intervalAccepted0539 (fun t => piece_le_psi ⟨499,by decide +kernel⟩ t)
def piece0540 : AffinePiece := pieces[500]'(by decide +kernel)
theorem intervalAccepted0540 : candidateIntervalCheck candidate0540 (329/2000) (1647/10000) piece0540=true := by decide +kernel
noncomputable def cell0540 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0540 accepted0540 (329/2000) (1647/10000) piece0540
    intervalAccepted0540 (fun t => piece_le_psi ⟨500,by decide +kernel⟩ t)
def piece0541 : AffinePiece := pieces[501]'(by decide +kernel)
theorem intervalAccepted0541 : candidateIntervalCheck candidate0541 (1647/10000) (1649/10000) piece0541=true := by decide +kernel
noncomputable def cell0541 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0541 accepted0541 (1647/10000) (1649/10000) piece0541
    intervalAccepted0541 (fun t => piece_le_psi ⟨501,by decide +kernel⟩ t)
def piece0542 : AffinePiece := pieces[502]'(by decide +kernel)
theorem intervalAccepted0542 : candidateIntervalCheck candidate0542 (1649/10000) (1651/10000) piece0542=true := by decide +kernel
noncomputable def cell0542 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0542 accepted0542 (1649/10000) (1651/10000) piece0542
    intervalAccepted0542 (fun t => piece_le_psi ⟨502,by decide +kernel⟩ t)
def piece0543 : AffinePiece := pieces[503]'(by decide +kernel)
theorem intervalAccepted0543 : candidateIntervalCheck candidate0543 (1651/10000) (1653/10000) piece0543=true := by decide +kernel
noncomputable def cell0543 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0543 accepted0543 (1651/10000) (1653/10000) piece0543
    intervalAccepted0543 (fun t => piece_le_psi ⟨503,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0528, cell0529, cell0530, cell0531, cell0532, cell0533, cell0534, cell0535, cell0536, cell0537, cell0538, cell0539, cell0540, cell0541, cell0542, cell0543]
theorem chainAccepted : spinCellChainCheck (1621/10000) (1653/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1621/10000) (1653/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0033
