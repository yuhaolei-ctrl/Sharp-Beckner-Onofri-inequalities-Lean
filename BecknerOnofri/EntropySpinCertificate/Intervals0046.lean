module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0046

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0046
open CandidateBatch0046 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0736 : AffinePiece := pieces[634]'(by decide +kernel)
theorem intervalAccepted0736 : candidateIntervalCheck candidate0736 (109/500) (219/1000) piece0736=true := by decide +kernel
noncomputable def cell0736 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0736 accepted0736 (109/500) (219/1000) piece0736
    intervalAccepted0736 (fun t => piece_le_psi ⟨634,by decide +kernel⟩ t)
def piece0737 : AffinePiece := pieces[635]'(by decide +kernel)
theorem intervalAccepted0737 : candidateIntervalCheck candidate0737 (219/1000) (11/50) piece0737=true := by decide +kernel
noncomputable def cell0737 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0737 accepted0737 (219/1000) (11/50) piece0737
    intervalAccepted0737 (fun t => piece_le_psi ⟨635,by decide +kernel⟩ t)
def piece0738 : AffinePiece := pieces[636]'(by decide +kernel)
theorem intervalAccepted0738 : candidateIntervalCheck candidate0738 (11/50) (221/1000) piece0738=true := by decide +kernel
noncomputable def cell0738 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0738 accepted0738 (11/50) (221/1000) piece0738
    intervalAccepted0738 (fun t => piece_le_psi ⟨636,by decide +kernel⟩ t)
def piece0739 : AffinePiece := pieces[637]'(by decide +kernel)
theorem intervalAccepted0739 : candidateIntervalCheck candidate0739 (221/1000) (111/500) piece0739=true := by decide +kernel
noncomputable def cell0739 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0739 accepted0739 (221/1000) (111/500) piece0739
    intervalAccepted0739 (fun t => piece_le_psi ⟨637,by decide +kernel⟩ t)
def piece0740 : AffinePiece := pieces[638]'(by decide +kernel)
theorem intervalAccepted0740 : candidateIntervalCheck candidate0740 (111/500) (223/1000) piece0740=true := by decide +kernel
noncomputable def cell0740 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0740 accepted0740 (111/500) (223/1000) piece0740
    intervalAccepted0740 (fun t => piece_le_psi ⟨638,by decide +kernel⟩ t)
def piece0741 : AffinePiece := pieces[639]'(by decide +kernel)
theorem intervalAccepted0741 : candidateIntervalCheck candidate0741 (223/1000) (28/125) piece0741=true := by decide +kernel
noncomputable def cell0741 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0741 accepted0741 (223/1000) (28/125) piece0741
    intervalAccepted0741 (fun t => piece_le_psi ⟨639,by decide +kernel⟩ t)
def piece0742 : AffinePiece := pieces[640]'(by decide +kernel)
theorem intervalAccepted0742 : candidateIntervalCheck candidate0742 (28/125) (9/40) piece0742=true := by decide +kernel
noncomputable def cell0742 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0742 accepted0742 (28/125) (9/40) piece0742
    intervalAccepted0742 (fun t => piece_le_psi ⟨640,by decide +kernel⟩ t)
def piece0743 : AffinePiece := pieces[641]'(by decide +kernel)
theorem intervalAccepted0743 : candidateIntervalCheck candidate0743 (9/40) (113/500) piece0743=true := by decide +kernel
noncomputable def cell0743 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0743 accepted0743 (9/40) (113/500) piece0743
    intervalAccepted0743 (fun t => piece_le_psi ⟨641,by decide +kernel⟩ t)
def piece0744 : AffinePiece := pieces[642]'(by decide +kernel)
theorem intervalAccepted0744 : candidateIntervalCheck candidate0744 (113/500) (227/1000) piece0744=true := by decide +kernel
noncomputable def cell0744 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0744 accepted0744 (113/500) (227/1000) piece0744
    intervalAccepted0744 (fun t => piece_le_psi ⟨642,by decide +kernel⟩ t)
def piece0745 : AffinePiece := pieces[643]'(by decide +kernel)
theorem intervalAccepted0745 : candidateIntervalCheck candidate0745 (227/1000) (57/250) piece0745=true := by decide +kernel
noncomputable def cell0745 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0745 accepted0745 (227/1000) (57/250) piece0745
    intervalAccepted0745 (fun t => piece_le_psi ⟨643,by decide +kernel⟩ t)
def piece0746 : AffinePiece := pieces[644]'(by decide +kernel)
theorem intervalAccepted0746 : candidateIntervalCheck candidate0746 (57/250) (229/1000) piece0746=true := by decide +kernel
noncomputable def cell0746 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0746 accepted0746 (57/250) (229/1000) piece0746
    intervalAccepted0746 (fun t => piece_le_psi ⟨644,by decide +kernel⟩ t)
def piece0747 : AffinePiece := pieces[645]'(by decide +kernel)
theorem intervalAccepted0747 : candidateIntervalCheck candidate0747 (229/1000) (23/100) piece0747=true := by decide +kernel
noncomputable def cell0747 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0747 accepted0747 (229/1000) (23/100) piece0747
    intervalAccepted0747 (fun t => piece_le_psi ⟨645,by decide +kernel⟩ t)
def piece0748 : AffinePiece := pieces[646]'(by decide +kernel)
theorem intervalAccepted0748 : candidateIntervalCheck candidate0748 (23/100) (231/1000) piece0748=true := by decide +kernel
noncomputable def cell0748 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0748 accepted0748 (23/100) (231/1000) piece0748
    intervalAccepted0748 (fun t => piece_le_psi ⟨646,by decide +kernel⟩ t)
def piece0749 : AffinePiece := pieces[647]'(by decide +kernel)
theorem intervalAccepted0749 : candidateIntervalCheck candidate0749 (231/1000) (29/125) piece0749=true := by decide +kernel
noncomputable def cell0749 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0749 accepted0749 (231/1000) (29/125) piece0749
    intervalAccepted0749 (fun t => piece_le_psi ⟨647,by decide +kernel⟩ t)
def piece0750 : AffinePiece := pieces[648]'(by decide +kernel)
theorem intervalAccepted0750 : candidateIntervalCheck candidate0750 (29/125) (233/1000) piece0750=true := by decide +kernel
noncomputable def cell0750 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0750 accepted0750 (29/125) (233/1000) piece0750
    intervalAccepted0750 (fun t => piece_le_psi ⟨648,by decide +kernel⟩ t)
def piece0751 : AffinePiece := pieces[649]'(by decide +kernel)
theorem intervalAccepted0751 : candidateIntervalCheck candidate0751 (233/1000) (117/500) piece0751=true := by decide +kernel
noncomputable def cell0751 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0751 accepted0751 (233/1000) (117/500) piece0751
    intervalAccepted0751 (fun t => piece_le_psi ⟨649,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0736, cell0737, cell0738, cell0739, cell0740, cell0741, cell0742, cell0743, cell0744, cell0745, cell0746, cell0747, cell0748, cell0749, cell0750, cell0751]
theorem chainAccepted : spinCellChainCheck (109/500) (117/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (109/500) (117/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0046
