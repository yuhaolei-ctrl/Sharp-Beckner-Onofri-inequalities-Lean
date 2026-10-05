module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0035

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0035
open CandidateBatch0035 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0560 : AffinePiece := pieces[520]'(by decide +kernel)
theorem intervalAccepted0560 : candidateIntervalCheck candidate0560 (337/2000) (1687/10000) piece0560=true := by decide +kernel
noncomputable def cell0560 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0560 accepted0560 (337/2000) (1687/10000) piece0560
    intervalAccepted0560 (fun t => piece_le_psi ⟨520,by decide +kernel⟩ t)
def piece0561 : AffinePiece := pieces[521]'(by decide +kernel)
theorem intervalAccepted0561 : candidateIntervalCheck candidate0561 (1687/10000) (1689/10000) piece0561=true := by decide +kernel
noncomputable def cell0561 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0561 accepted0561 (1687/10000) (1689/10000) piece0561
    intervalAccepted0561 (fun t => piece_le_psi ⟨521,by decide +kernel⟩ t)
def piece0562 : AffinePiece := pieces[522]'(by decide +kernel)
theorem intervalAccepted0562 : candidateIntervalCheck candidate0562 (1689/10000) (1691/10000) piece0562=true := by decide +kernel
noncomputable def cell0562 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0562 accepted0562 (1689/10000) (1691/10000) piece0562
    intervalAccepted0562 (fun t => piece_le_psi ⟨522,by decide +kernel⟩ t)
def piece0563 : AffinePiece := pieces[523]'(by decide +kernel)
theorem intervalAccepted0563 : candidateIntervalCheck candidate0563 (1691/10000) (1693/10000) piece0563=true := by decide +kernel
noncomputable def cell0563 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0563 accepted0563 (1691/10000) (1693/10000) piece0563
    intervalAccepted0563 (fun t => piece_le_psi ⟨523,by decide +kernel⟩ t)
def piece0564 : AffinePiece := pieces[524]'(by decide +kernel)
theorem intervalAccepted0564 : candidateIntervalCheck candidate0564 (1693/10000) (339/2000) piece0564=true := by decide +kernel
noncomputable def cell0564 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0564 accepted0564 (1693/10000) (339/2000) piece0564
    intervalAccepted0564 (fun t => piece_le_psi ⟨524,by decide +kernel⟩ t)
def piece0565 : AffinePiece := pieces[525]'(by decide +kernel)
theorem intervalAccepted0565 : candidateIntervalCheck candidate0565 (339/2000) (1697/10000) piece0565=true := by decide +kernel
noncomputable def cell0565 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0565 accepted0565 (339/2000) (1697/10000) piece0565
    intervalAccepted0565 (fun t => piece_le_psi ⟨525,by decide +kernel⟩ t)
def piece0566 : AffinePiece := pieces[526]'(by decide +kernel)
theorem intervalAccepted0566 : candidateIntervalCheck candidate0566 (1697/10000) (1699/10000) piece0566=true := by decide +kernel
noncomputable def cell0566 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0566 accepted0566 (1697/10000) (1699/10000) piece0566
    intervalAccepted0566 (fun t => piece_le_psi ⟨526,by decide +kernel⟩ t)
def piece0567 : AffinePiece := pieces[527]'(by decide +kernel)
theorem intervalAccepted0567 : candidateIntervalCheck candidate0567 (1699/10000) (1701/10000) piece0567=true := by decide +kernel
noncomputable def cell0567 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0567 accepted0567 (1699/10000) (1701/10000) piece0567
    intervalAccepted0567 (fun t => piece_le_psi ⟨527,by decide +kernel⟩ t)
def piece0568 : AffinePiece := pieces[528]'(by decide +kernel)
theorem intervalAccepted0568 : candidateIntervalCheck candidate0568 (1701/10000) (1703/10000) piece0568=true := by decide +kernel
noncomputable def cell0568 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0568 accepted0568 (1701/10000) (1703/10000) piece0568
    intervalAccepted0568 (fun t => piece_le_psi ⟨528,by decide +kernel⟩ t)
def piece0569 : AffinePiece := pieces[529]'(by decide +kernel)
theorem intervalAccepted0569 : candidateIntervalCheck candidate0569 (1703/10000) (341/2000) piece0569=true := by decide +kernel
noncomputable def cell0569 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0569 accepted0569 (1703/10000) (341/2000) piece0569
    intervalAccepted0569 (fun t => piece_le_psi ⟨529,by decide +kernel⟩ t)
def piece0570 : AffinePiece := pieces[530]'(by decide +kernel)
theorem intervalAccepted0570 : candidateIntervalCheck candidate0570 (341/2000) (1707/10000) piece0570=true := by decide +kernel
noncomputable def cell0570 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0570 accepted0570 (341/2000) (1707/10000) piece0570
    intervalAccepted0570 (fun t => piece_le_psi ⟨530,by decide +kernel⟩ t)
def piece0571 : AffinePiece := pieces[531]'(by decide +kernel)
theorem intervalAccepted0571 : candidateIntervalCheck candidate0571 (1707/10000) (1709/10000) piece0571=true := by decide +kernel
noncomputable def cell0571 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0571 accepted0571 (1707/10000) (1709/10000) piece0571
    intervalAccepted0571 (fun t => piece_le_psi ⟨531,by decide +kernel⟩ t)
def piece0572 : AffinePiece := pieces[532]'(by decide +kernel)
theorem intervalAccepted0572 : candidateIntervalCheck candidate0572 (1709/10000) (1711/10000) piece0572=true := by decide +kernel
noncomputable def cell0572 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0572 accepted0572 (1709/10000) (1711/10000) piece0572
    intervalAccepted0572 (fun t => piece_le_psi ⟨532,by decide +kernel⟩ t)
def piece0573 : AffinePiece := pieces[533]'(by decide +kernel)
theorem intervalAccepted0573 : candidateIntervalCheck candidate0573 (1711/10000) (1713/10000) piece0573=true := by decide +kernel
noncomputable def cell0573 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0573 accepted0573 (1711/10000) (1713/10000) piece0573
    intervalAccepted0573 (fun t => piece_le_psi ⟨533,by decide +kernel⟩ t)
def piece0574 : AffinePiece := pieces[534]'(by decide +kernel)
theorem intervalAccepted0574 : candidateIntervalCheck candidate0574 (1713/10000) (343/2000) piece0574=true := by decide +kernel
noncomputable def cell0574 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0574 accepted0574 (1713/10000) (343/2000) piece0574
    intervalAccepted0574 (fun t => piece_le_psi ⟨534,by decide +kernel⟩ t)
def piece0575 : AffinePiece := pieces[535]'(by decide +kernel)
theorem intervalAccepted0575 : candidateIntervalCheck candidate0575 (343/2000) (1717/10000) piece0575=true := by decide +kernel
noncomputable def cell0575 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0575 accepted0575 (343/2000) (1717/10000) piece0575
    intervalAccepted0575 (fun t => piece_le_psi ⟨535,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0560, cell0561, cell0562, cell0563, cell0564, cell0565, cell0566, cell0567, cell0568, cell0569, cell0570, cell0571, cell0572, cell0573, cell0574, cell0575]
theorem chainAccepted : spinCellChainCheck (337/2000) (1717/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (337/2000) (1717/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0035
