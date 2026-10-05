import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0047
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0047
open CandidateBatch0047 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0752 : AffinePiece := pieces[650]'(by decide +kernel)
theorem intervalAccepted0752 : candidateIntervalCheck candidate0752 (117/500) (47/200) piece0752=true := by decide +kernel
noncomputable def cell0752 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0752 accepted0752 (117/500) (47/200) piece0752
    intervalAccepted0752 (fun t => piece_le_psi ⟨650,by decide +kernel⟩ t)
def piece0753 : AffinePiece := pieces[651]'(by decide +kernel)
theorem intervalAccepted0753 : candidateIntervalCheck candidate0753 (47/200) (59/250) piece0753=true := by decide +kernel
noncomputable def cell0753 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0753 accepted0753 (47/200) (59/250) piece0753
    intervalAccepted0753 (fun t => piece_le_psi ⟨651,by decide +kernel⟩ t)
def piece0754 : AffinePiece := pieces[652]'(by decide +kernel)
theorem intervalAccepted0754 : candidateIntervalCheck candidate0754 (59/250) (237/1000) piece0754=true := by decide +kernel
noncomputable def cell0754 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0754 accepted0754 (59/250) (237/1000) piece0754
    intervalAccepted0754 (fun t => piece_le_psi ⟨652,by decide +kernel⟩ t)
def piece0755 : AffinePiece := pieces[653]'(by decide +kernel)
theorem intervalAccepted0755 : candidateIntervalCheck candidate0755 (237/1000) (119/500) piece0755=true := by decide +kernel
noncomputable def cell0755 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0755 accepted0755 (237/1000) (119/500) piece0755
    intervalAccepted0755 (fun t => piece_le_psi ⟨653,by decide +kernel⟩ t)
def piece0756 : AffinePiece := pieces[654]'(by decide +kernel)
theorem intervalAccepted0756 : candidateIntervalCheck candidate0756 (119/500) (239/1000) piece0756=true := by decide +kernel
noncomputable def cell0756 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0756 accepted0756 (119/500) (239/1000) piece0756
    intervalAccepted0756 (fun t => piece_le_psi ⟨654,by decide +kernel⟩ t)
def piece0757 : AffinePiece := pieces[655]'(by decide +kernel)
theorem intervalAccepted0757 : candidateIntervalCheck candidate0757 (239/1000) (6/25) piece0757=true := by decide +kernel
noncomputable def cell0757 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0757 accepted0757 (239/1000) (6/25) piece0757
    intervalAccepted0757 (fun t => piece_le_psi ⟨655,by decide +kernel⟩ t)
def piece0758 : AffinePiece := pieces[656]'(by decide +kernel)
theorem intervalAccepted0758 : candidateIntervalCheck candidate0758 (6/25) (241/1000) piece0758=true := by decide +kernel
noncomputable def cell0758 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0758 accepted0758 (6/25) (241/1000) piece0758
    intervalAccepted0758 (fun t => piece_le_psi ⟨656,by decide +kernel⟩ t)
def piece0759 : AffinePiece := pieces[657]'(by decide +kernel)
theorem intervalAccepted0759 : candidateIntervalCheck candidate0759 (241/1000) (121/500) piece0759=true := by decide +kernel
noncomputable def cell0759 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0759 accepted0759 (241/1000) (121/500) piece0759
    intervalAccepted0759 (fun t => piece_le_psi ⟨657,by decide +kernel⟩ t)
def piece0760 : AffinePiece := pieces[658]'(by decide +kernel)
theorem intervalAccepted0760 : candidateIntervalCheck candidate0760 (121/500) (243/1000) piece0760=true := by decide +kernel
noncomputable def cell0760 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0760 accepted0760 (121/500) (243/1000) piece0760
    intervalAccepted0760 (fun t => piece_le_psi ⟨658,by decide +kernel⟩ t)
def piece0761 : AffinePiece := pieces[659]'(by decide +kernel)
theorem intervalAccepted0761 : candidateIntervalCheck candidate0761 (243/1000) (61/250) piece0761=true := by decide +kernel
noncomputable def cell0761 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0761 accepted0761 (243/1000) (61/250) piece0761
    intervalAccepted0761 (fun t => piece_le_psi ⟨659,by decide +kernel⟩ t)
def piece0762 : AffinePiece := pieces[660]'(by decide +kernel)
theorem intervalAccepted0762 : candidateIntervalCheck candidate0762 (61/250) (49/200) piece0762=true := by decide +kernel
noncomputable def cell0762 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0762 accepted0762 (61/250) (49/200) piece0762
    intervalAccepted0762 (fun t => piece_le_psi ⟨660,by decide +kernel⟩ t)
def piece0763 : AffinePiece := pieces[661]'(by decide +kernel)
theorem intervalAccepted0763 : candidateIntervalCheck candidate0763 (49/200) (123/500) piece0763=true := by decide +kernel
noncomputable def cell0763 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0763 accepted0763 (49/200) (123/500) piece0763
    intervalAccepted0763 (fun t => piece_le_psi ⟨661,by decide +kernel⟩ t)
def piece0764 : AffinePiece := pieces[662]'(by decide +kernel)
theorem intervalAccepted0764 : candidateIntervalCheck candidate0764 (123/500) (247/1000) piece0764=true := by decide +kernel
noncomputable def cell0764 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0764 accepted0764 (123/500) (247/1000) piece0764
    intervalAccepted0764 (fun t => piece_le_psi ⟨662,by decide +kernel⟩ t)
def piece0765 : AffinePiece := pieces[663]'(by decide +kernel)
theorem intervalAccepted0765 : candidateIntervalCheck candidate0765 (247/1000) (31/125) piece0765=true := by decide +kernel
noncomputable def cell0765 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0765 accepted0765 (247/1000) (31/125) piece0765
    intervalAccepted0765 (fun t => piece_le_psi ⟨663,by decide +kernel⟩ t)
def piece0766 : AffinePiece := pieces[664]'(by decide +kernel)
theorem intervalAccepted0766 : candidateIntervalCheck candidate0766 (31/125) (249/1000) piece0766=true := by decide +kernel
noncomputable def cell0766 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0766 accepted0766 (31/125) (249/1000) piece0766
    intervalAccepted0766 (fun t => piece_le_psi ⟨664,by decide +kernel⟩ t)
def piece0767 : AffinePiece := pieces[665]'(by decide +kernel)
theorem intervalAccepted0767 : candidateIntervalCheck candidate0767 (249/1000) (1/4) piece0767=true := by decide +kernel
noncomputable def cell0767 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0767 accepted0767 (249/1000) (1/4) piece0767
    intervalAccepted0767 (fun t => piece_le_psi ⟨665,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0752, cell0753, cell0754, cell0755, cell0756, cell0757, cell0758, cell0759, cell0760, cell0761, cell0762, cell0763, cell0764, cell0765, cell0766, cell0767]
theorem chainAccepted : spinCellChainCheck (117/500) (1/4) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (117/500) (1/4) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0047
