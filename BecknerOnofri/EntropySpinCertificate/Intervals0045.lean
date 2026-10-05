import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0045
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0045
open CandidateBatch0045 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0720 : AffinePiece := pieces[618]'(by decide +kernel)
theorem intervalAccepted0720 : candidateIntervalCheck candidate0720 (101/500) (203/1000) piece0720=true := by decide +kernel
noncomputable def cell0720 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0720 accepted0720 (101/500) (203/1000) piece0720
    intervalAccepted0720 (fun t => piece_le_psi ⟨618,by decide +kernel⟩ t)
def piece0721 : AffinePiece := pieces[619]'(by decide +kernel)
theorem intervalAccepted0721 : candidateIntervalCheck candidate0721 (203/1000) (51/250) piece0721=true := by decide +kernel
noncomputable def cell0721 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0721 accepted0721 (203/1000) (51/250) piece0721
    intervalAccepted0721 (fun t => piece_le_psi ⟨619,by decide +kernel⟩ t)
def piece0722 : AffinePiece := pieces[620]'(by decide +kernel)
theorem intervalAccepted0722 : candidateIntervalCheck candidate0722 (51/250) (41/200) piece0722=true := by decide +kernel
noncomputable def cell0722 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0722 accepted0722 (51/250) (41/200) piece0722
    intervalAccepted0722 (fun t => piece_le_psi ⟨620,by decide +kernel⟩ t)
def piece0723 : AffinePiece := pieces[621]'(by decide +kernel)
theorem intervalAccepted0723 : candidateIntervalCheck candidate0723 (41/200) (103/500) piece0723=true := by decide +kernel
noncomputable def cell0723 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0723 accepted0723 (41/200) (103/500) piece0723
    intervalAccepted0723 (fun t => piece_le_psi ⟨621,by decide +kernel⟩ t)
def piece0724 : AffinePiece := pieces[622]'(by decide +kernel)
theorem intervalAccepted0724 : candidateIntervalCheck candidate0724 (103/500) (207/1000) piece0724=true := by decide +kernel
noncomputable def cell0724 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0724 accepted0724 (103/500) (207/1000) piece0724
    intervalAccepted0724 (fun t => piece_le_psi ⟨622,by decide +kernel⟩ t)
def piece0725 : AffinePiece := pieces[623]'(by decide +kernel)
theorem intervalAccepted0725 : candidateIntervalCheck candidate0725 (207/1000) (26/125) piece0725=true := by decide +kernel
noncomputable def cell0725 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0725 accepted0725 (207/1000) (26/125) piece0725
    intervalAccepted0725 (fun t => piece_le_psi ⟨623,by decide +kernel⟩ t)
def piece0726 : AffinePiece := pieces[624]'(by decide +kernel)
theorem intervalAccepted0726 : candidateIntervalCheck candidate0726 (26/125) (209/1000) piece0726=true := by decide +kernel
noncomputable def cell0726 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0726 accepted0726 (26/125) (209/1000) piece0726
    intervalAccepted0726 (fun t => piece_le_psi ⟨624,by decide +kernel⟩ t)
def piece0727 : AffinePiece := pieces[625]'(by decide +kernel)
theorem intervalAccepted0727 : candidateIntervalCheck candidate0727 (209/1000) (21/100) piece0727=true := by decide +kernel
noncomputable def cell0727 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0727 accepted0727 (209/1000) (21/100) piece0727
    intervalAccepted0727 (fun t => piece_le_psi ⟨625,by decide +kernel⟩ t)
def piece0728 : AffinePiece := pieces[626]'(by decide +kernel)
theorem intervalAccepted0728 : candidateIntervalCheck candidate0728 (21/100) (211/1000) piece0728=true := by decide +kernel
noncomputable def cell0728 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0728 accepted0728 (21/100) (211/1000) piece0728
    intervalAccepted0728 (fun t => piece_le_psi ⟨626,by decide +kernel⟩ t)
def piece0729 : AffinePiece := pieces[627]'(by decide +kernel)
theorem intervalAccepted0729 : candidateIntervalCheck candidate0729 (211/1000) (53/250) piece0729=true := by decide +kernel
noncomputable def cell0729 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0729 accepted0729 (211/1000) (53/250) piece0729
    intervalAccepted0729 (fun t => piece_le_psi ⟨627,by decide +kernel⟩ t)
def piece0730 : AffinePiece := pieces[628]'(by decide +kernel)
theorem intervalAccepted0730 : candidateIntervalCheck candidate0730 (53/250) (213/1000) piece0730=true := by decide +kernel
noncomputable def cell0730 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0730 accepted0730 (53/250) (213/1000) piece0730
    intervalAccepted0730 (fun t => piece_le_psi ⟨628,by decide +kernel⟩ t)
def piece0731 : AffinePiece := pieces[629]'(by decide +kernel)
theorem intervalAccepted0731 : candidateIntervalCheck candidate0731 (213/1000) (107/500) piece0731=true := by decide +kernel
noncomputable def cell0731 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0731 accepted0731 (213/1000) (107/500) piece0731
    intervalAccepted0731 (fun t => piece_le_psi ⟨629,by decide +kernel⟩ t)
def piece0732 : AffinePiece := pieces[630]'(by decide +kernel)
theorem intervalAccepted0732 : candidateIntervalCheck candidate0732 (107/500) (43/200) piece0732=true := by decide +kernel
noncomputable def cell0732 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0732 accepted0732 (107/500) (43/200) piece0732
    intervalAccepted0732 (fun t => piece_le_psi ⟨630,by decide +kernel⟩ t)
def piece0733 : AffinePiece := pieces[631]'(by decide +kernel)
theorem intervalAccepted0733 : candidateIntervalCheck candidate0733 (43/200) (27/125) piece0733=true := by decide +kernel
noncomputable def cell0733 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0733 accepted0733 (43/200) (27/125) piece0733
    intervalAccepted0733 (fun t => piece_le_psi ⟨631,by decide +kernel⟩ t)
def piece0734 : AffinePiece := pieces[632]'(by decide +kernel)
theorem intervalAccepted0734 : candidateIntervalCheck candidate0734 (27/125) (217/1000) piece0734=true := by decide +kernel
noncomputable def cell0734 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0734 accepted0734 (27/125) (217/1000) piece0734
    intervalAccepted0734 (fun t => piece_le_psi ⟨632,by decide +kernel⟩ t)
def piece0735 : AffinePiece := pieces[633]'(by decide +kernel)
theorem intervalAccepted0735 : candidateIntervalCheck candidate0735 (217/1000) (109/500) piece0735=true := by decide +kernel
noncomputable def cell0735 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0735 accepted0735 (217/1000) (109/500) piece0735
    intervalAccepted0735 (fun t => piece_le_psi ⟨633,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0720, cell0721, cell0722, cell0723, cell0724, cell0725, cell0726, cell0727, cell0728, cell0729, cell0730, cell0731, cell0732, cell0733, cell0734, cell0735]
theorem chainAccepted : spinCellChainCheck (101/500) (109/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (101/500) (109/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0045
