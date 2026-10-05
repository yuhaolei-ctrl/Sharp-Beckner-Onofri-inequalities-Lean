module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0036

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0036
open CandidateBatch0036 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0576 : AffinePiece := pieces[536]'(by decide +kernel)
theorem intervalAccepted0576 : candidateIntervalCheck candidate0576 (1717/10000) (1719/10000) piece0576=true := by decide +kernel
noncomputable def cell0576 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0576 accepted0576 (1717/10000) (1719/10000) piece0576
    intervalAccepted0576 (fun t => piece_le_psi ⟨536,by decide +kernel⟩ t)
def piece0577 : AffinePiece := pieces[537]'(by decide +kernel)
theorem intervalAccepted0577 : candidateIntervalCheck candidate0577 (1719/10000) (1721/10000) piece0577=true := by decide +kernel
noncomputable def cell0577 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0577 accepted0577 (1719/10000) (1721/10000) piece0577
    intervalAccepted0577 (fun t => piece_le_psi ⟨537,by decide +kernel⟩ t)
def piece0578 : AffinePiece := pieces[538]'(by decide +kernel)
theorem intervalAccepted0578 : candidateIntervalCheck candidate0578 (1721/10000) (1723/10000) piece0578=true := by decide +kernel
noncomputable def cell0578 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0578 accepted0578 (1721/10000) (1723/10000) piece0578
    intervalAccepted0578 (fun t => piece_le_psi ⟨538,by decide +kernel⟩ t)
def piece0579 : AffinePiece := pieces[539]'(by decide +kernel)
theorem intervalAccepted0579 : candidateIntervalCheck candidate0579 (1723/10000) (69/400) piece0579=true := by decide +kernel
noncomputable def cell0579 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0579 accepted0579 (1723/10000) (69/400) piece0579
    intervalAccepted0579 (fun t => piece_le_psi ⟨539,by decide +kernel⟩ t)
def piece0580 : AffinePiece := pieces[540]'(by decide +kernel)
theorem intervalAccepted0580 : candidateIntervalCheck candidate0580 (69/400) (1727/10000) piece0580=true := by decide +kernel
noncomputable def cell0580 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0580 accepted0580 (69/400) (1727/10000) piece0580
    intervalAccepted0580 (fun t => piece_le_psi ⟨540,by decide +kernel⟩ t)
def piece0581 : AffinePiece := pieces[541]'(by decide +kernel)
theorem intervalAccepted0581 : candidateIntervalCheck candidate0581 (1727/10000) (1729/10000) piece0581=true := by decide +kernel
noncomputable def cell0581 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0581 accepted0581 (1727/10000) (1729/10000) piece0581
    intervalAccepted0581 (fun t => piece_le_psi ⟨541,by decide +kernel⟩ t)
def piece0582 : AffinePiece := pieces[542]'(by decide +kernel)
theorem intervalAccepted0582 : candidateIntervalCheck candidate0582 (1729/10000) (1731/10000) piece0582=true := by decide +kernel
noncomputable def cell0582 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0582 accepted0582 (1729/10000) (1731/10000) piece0582
    intervalAccepted0582 (fun t => piece_le_psi ⟨542,by decide +kernel⟩ t)
def piece0583 : AffinePiece := pieces[543]'(by decide +kernel)
theorem intervalAccepted0583 : candidateIntervalCheck candidate0583 (1731/10000) (1733/10000) piece0583=true := by decide +kernel
noncomputable def cell0583 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0583 accepted0583 (1731/10000) (1733/10000) piece0583
    intervalAccepted0583 (fun t => piece_le_psi ⟨543,by decide +kernel⟩ t)
def piece0584 : AffinePiece := pieces[544]'(by decide +kernel)
theorem intervalAccepted0584 : candidateIntervalCheck candidate0584 (1733/10000) (347/2000) piece0584=true := by decide +kernel
noncomputable def cell0584 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0584 accepted0584 (1733/10000) (347/2000) piece0584
    intervalAccepted0584 (fun t => piece_le_psi ⟨544,by decide +kernel⟩ t)
def piece0585 : AffinePiece := pieces[545]'(by decide +kernel)
theorem intervalAccepted0585 : candidateIntervalCheck candidate0585 (347/2000) (1737/10000) piece0585=true := by decide +kernel
noncomputable def cell0585 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0585 accepted0585 (347/2000) (1737/10000) piece0585
    intervalAccepted0585 (fun t => piece_le_psi ⟨545,by decide +kernel⟩ t)
def piece0586 : AffinePiece := pieces[546]'(by decide +kernel)
theorem intervalAccepted0586 : candidateIntervalCheck candidate0586 (1737/10000) (1739/10000) piece0586=true := by decide +kernel
noncomputable def cell0586 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0586 accepted0586 (1737/10000) (1739/10000) piece0586
    intervalAccepted0586 (fun t => piece_le_psi ⟨546,by decide +kernel⟩ t)
def piece0587 : AffinePiece := pieces[547]'(by decide +kernel)
theorem intervalAccepted0587 : candidateIntervalCheck candidate0587 (1739/10000) (1741/10000) piece0587=true := by decide +kernel
noncomputable def cell0587 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0587 accepted0587 (1739/10000) (1741/10000) piece0587
    intervalAccepted0587 (fun t => piece_le_psi ⟨547,by decide +kernel⟩ t)
def piece0588 : AffinePiece := pieces[548]'(by decide +kernel)
theorem intervalAccepted0588 : candidateIntervalCheck candidate0588 (1741/10000) (1743/10000) piece0588=true := by decide +kernel
noncomputable def cell0588 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0588 accepted0588 (1741/10000) (1743/10000) piece0588
    intervalAccepted0588 (fun t => piece_le_psi ⟨548,by decide +kernel⟩ t)
def piece0589 : AffinePiece := pieces[549]'(by decide +kernel)
theorem intervalAccepted0589 : candidateIntervalCheck candidate0589 (1743/10000) (349/2000) piece0589=true := by decide +kernel
noncomputable def cell0589 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0589 accepted0589 (1743/10000) (349/2000) piece0589
    intervalAccepted0589 (fun t => piece_le_psi ⟨549,by decide +kernel⟩ t)
def piece0590 : AffinePiece := pieces[550]'(by decide +kernel)
theorem intervalAccepted0590 : candidateIntervalCheck candidate0590 (349/2000) (1747/10000) piece0590=true := by decide +kernel
noncomputable def cell0590 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0590 accepted0590 (349/2000) (1747/10000) piece0590
    intervalAccepted0590 (fun t => piece_le_psi ⟨550,by decide +kernel⟩ t)
def piece0591 : AffinePiece := pieces[551]'(by decide +kernel)
theorem intervalAccepted0591 : candidateIntervalCheck candidate0591 (1747/10000) (1749/10000) piece0591=true := by decide +kernel
noncomputable def cell0591 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0591 accepted0591 (1747/10000) (1749/10000) piece0591
    intervalAccepted0591 (fun t => piece_le_psi ⟨551,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0576, cell0577, cell0578, cell0579, cell0580, cell0581, cell0582, cell0583, cell0584, cell0585, cell0586, cell0587, cell0588, cell0589, cell0590, cell0591]
theorem chainAccepted : spinCellChainCheck (1717/10000) (1749/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1717/10000) (1749/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0036
