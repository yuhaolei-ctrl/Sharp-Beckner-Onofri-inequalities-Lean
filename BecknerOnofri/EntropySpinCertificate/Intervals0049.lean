import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0049
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0049
open CandidateBatch0049 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0784 : AffinePiece := pieces[682]'(by decide +kernel)
theorem intervalAccepted0784 : candidateIntervalCheck candidate0784 (133/500) (267/1000) piece0784=true := by decide +kernel
noncomputable def cell0784 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0784 accepted0784 (133/500) (267/1000) piece0784
    intervalAccepted0784 (fun t => piece_le_psi ⟨682,by decide +kernel⟩ t)
def piece0785 : AffinePiece := pieces[683]'(by decide +kernel)
theorem intervalAccepted0785 : candidateIntervalCheck candidate0785 (267/1000) (67/250) piece0785=true := by decide +kernel
noncomputable def cell0785 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0785 accepted0785 (267/1000) (67/250) piece0785
    intervalAccepted0785 (fun t => piece_le_psi ⟨683,by decide +kernel⟩ t)
def piece0786 : AffinePiece := pieces[684]'(by decide +kernel)
theorem intervalAccepted0786 : candidateIntervalCheck candidate0786 (67/250) (269/1000) piece0786=true := by decide +kernel
noncomputable def cell0786 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0786 accepted0786 (67/250) (269/1000) piece0786
    intervalAccepted0786 (fun t => piece_le_psi ⟨684,by decide +kernel⟩ t)
def piece0787 : AffinePiece := pieces[685]'(by decide +kernel)
theorem intervalAccepted0787 : candidateIntervalCheck candidate0787 (269/1000) (27/100) piece0787=true := by decide +kernel
noncomputable def cell0787 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0787 accepted0787 (269/1000) (27/100) piece0787
    intervalAccepted0787 (fun t => piece_le_psi ⟨685,by decide +kernel⟩ t)
def piece0788 : AffinePiece := pieces[686]'(by decide +kernel)
theorem intervalAccepted0788 : candidateIntervalCheck candidate0788 (27/100) (271/1000) piece0788=true := by decide +kernel
noncomputable def cell0788 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0788 accepted0788 (27/100) (271/1000) piece0788
    intervalAccepted0788 (fun t => piece_le_psi ⟨686,by decide +kernel⟩ t)
def piece0789 : AffinePiece := pieces[687]'(by decide +kernel)
theorem intervalAccepted0789 : candidateIntervalCheck candidate0789 (271/1000) (34/125) piece0789=true := by decide +kernel
noncomputable def cell0789 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0789 accepted0789 (271/1000) (34/125) piece0789
    intervalAccepted0789 (fun t => piece_le_psi ⟨687,by decide +kernel⟩ t)
def piece0790 : AffinePiece := pieces[688]'(by decide +kernel)
theorem intervalAccepted0790 : candidateIntervalCheck candidate0790 (34/125) (273/1000) piece0790=true := by decide +kernel
noncomputable def cell0790 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0790 accepted0790 (34/125) (273/1000) piece0790
    intervalAccepted0790 (fun t => piece_le_psi ⟨688,by decide +kernel⟩ t)
def piece0791 : AffinePiece := pieces[689]'(by decide +kernel)
theorem intervalAccepted0791 : candidateIntervalCheck candidate0791 (273/1000) (137/500) piece0791=true := by decide +kernel
noncomputable def cell0791 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0791 accepted0791 (273/1000) (137/500) piece0791
    intervalAccepted0791 (fun t => piece_le_psi ⟨689,by decide +kernel⟩ t)
def piece0792 : AffinePiece := pieces[690]'(by decide +kernel)
theorem intervalAccepted0792 : candidateIntervalCheck candidate0792 (137/500) (11/40) piece0792=true := by decide +kernel
noncomputable def cell0792 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0792 accepted0792 (137/500) (11/40) piece0792
    intervalAccepted0792 (fun t => piece_le_psi ⟨690,by decide +kernel⟩ t)
def piece0793 : AffinePiece := pieces[691]'(by decide +kernel)
theorem intervalAccepted0793 : candidateIntervalCheck candidate0793 (11/40) (69/250) piece0793=true := by decide +kernel
noncomputable def cell0793 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0793 accepted0793 (11/40) (69/250) piece0793
    intervalAccepted0793 (fun t => piece_le_psi ⟨691,by decide +kernel⟩ t)
def piece0794 : AffinePiece := pieces[692]'(by decide +kernel)
theorem intervalAccepted0794 : candidateIntervalCheck candidate0794 (69/250) (277/1000) piece0794=true := by decide +kernel
noncomputable def cell0794 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0794 accepted0794 (69/250) (277/1000) piece0794
    intervalAccepted0794 (fun t => piece_le_psi ⟨692,by decide +kernel⟩ t)
def piece0795 : AffinePiece := pieces[693]'(by decide +kernel)
theorem intervalAccepted0795 : candidateIntervalCheck candidate0795 (277/1000) (139/500) piece0795=true := by decide +kernel
noncomputable def cell0795 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0795 accepted0795 (277/1000) (139/500) piece0795
    intervalAccepted0795 (fun t => piece_le_psi ⟨693,by decide +kernel⟩ t)
def piece0796 : AffinePiece := pieces[694]'(by decide +kernel)
theorem intervalAccepted0796 : candidateIntervalCheck candidate0796 (139/500) (279/1000) piece0796=true := by decide +kernel
noncomputable def cell0796 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0796 accepted0796 (139/500) (279/1000) piece0796
    intervalAccepted0796 (fun t => piece_le_psi ⟨694,by decide +kernel⟩ t)
def piece0797 : AffinePiece := pieces[695]'(by decide +kernel)
theorem intervalAccepted0797 : candidateIntervalCheck candidate0797 (279/1000) (7/25) piece0797=true := by decide +kernel
noncomputable def cell0797 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0797 accepted0797 (279/1000) (7/25) piece0797
    intervalAccepted0797 (fun t => piece_le_psi ⟨695,by decide +kernel⟩ t)
def piece0798 : AffinePiece := pieces[696]'(by decide +kernel)
theorem intervalAccepted0798 : candidateIntervalCheck candidate0798 (7/25) (281/1000) piece0798=true := by decide +kernel
noncomputable def cell0798 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0798 accepted0798 (7/25) (281/1000) piece0798
    intervalAccepted0798 (fun t => piece_le_psi ⟨696,by decide +kernel⟩ t)
def piece0799 : AffinePiece := pieces[697]'(by decide +kernel)
theorem intervalAccepted0799 : candidateIntervalCheck candidate0799 (281/1000) (141/500) piece0799=true := by decide +kernel
noncomputable def cell0799 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0799 accepted0799 (281/1000) (141/500) piece0799
    intervalAccepted0799 (fun t => piece_le_psi ⟨697,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0784, cell0785, cell0786, cell0787, cell0788, cell0789, cell0790, cell0791, cell0792, cell0793, cell0794, cell0795, cell0796, cell0797, cell0798, cell0799]
theorem chainAccepted : spinCellChainCheck (133/500) (141/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (133/500) (141/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0049
