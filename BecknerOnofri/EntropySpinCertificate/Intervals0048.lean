import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0048
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0048
open CandidateBatch0048 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0768 : AffinePiece := pieces[666]'(by decide +kernel)
theorem intervalAccepted0768 : candidateIntervalCheck candidate0768 (1/4) (251/1000) piece0768=true := by decide +kernel
noncomputable def cell0768 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0768 accepted0768 (1/4) (251/1000) piece0768
    intervalAccepted0768 (fun t => piece_le_psi ⟨666,by decide +kernel⟩ t)
def piece0769 : AffinePiece := pieces[667]'(by decide +kernel)
theorem intervalAccepted0769 : candidateIntervalCheck candidate0769 (251/1000) (63/250) piece0769=true := by decide +kernel
noncomputable def cell0769 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0769 accepted0769 (251/1000) (63/250) piece0769
    intervalAccepted0769 (fun t => piece_le_psi ⟨667,by decide +kernel⟩ t)
def piece0770 : AffinePiece := pieces[668]'(by decide +kernel)
theorem intervalAccepted0770 : candidateIntervalCheck candidate0770 (63/250) (253/1000) piece0770=true := by decide +kernel
noncomputable def cell0770 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0770 accepted0770 (63/250) (253/1000) piece0770
    intervalAccepted0770 (fun t => piece_le_psi ⟨668,by decide +kernel⟩ t)
def piece0771 : AffinePiece := pieces[669]'(by decide +kernel)
theorem intervalAccepted0771 : candidateIntervalCheck candidate0771 (253/1000) (127/500) piece0771=true := by decide +kernel
noncomputable def cell0771 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0771 accepted0771 (253/1000) (127/500) piece0771
    intervalAccepted0771 (fun t => piece_le_psi ⟨669,by decide +kernel⟩ t)
def piece0772 : AffinePiece := pieces[670]'(by decide +kernel)
theorem intervalAccepted0772 : candidateIntervalCheck candidate0772 (127/500) (51/200) piece0772=true := by decide +kernel
noncomputable def cell0772 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0772 accepted0772 (127/500) (51/200) piece0772
    intervalAccepted0772 (fun t => piece_le_psi ⟨670,by decide +kernel⟩ t)
def piece0773 : AffinePiece := pieces[671]'(by decide +kernel)
theorem intervalAccepted0773 : candidateIntervalCheck candidate0773 (51/200) (32/125) piece0773=true := by decide +kernel
noncomputable def cell0773 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0773 accepted0773 (51/200) (32/125) piece0773
    intervalAccepted0773 (fun t => piece_le_psi ⟨671,by decide +kernel⟩ t)
def piece0774 : AffinePiece := pieces[672]'(by decide +kernel)
theorem intervalAccepted0774 : candidateIntervalCheck candidate0774 (32/125) (257/1000) piece0774=true := by decide +kernel
noncomputable def cell0774 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0774 accepted0774 (32/125) (257/1000) piece0774
    intervalAccepted0774 (fun t => piece_le_psi ⟨672,by decide +kernel⟩ t)
def piece0775 : AffinePiece := pieces[673]'(by decide +kernel)
theorem intervalAccepted0775 : candidateIntervalCheck candidate0775 (257/1000) (129/500) piece0775=true := by decide +kernel
noncomputable def cell0775 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0775 accepted0775 (257/1000) (129/500) piece0775
    intervalAccepted0775 (fun t => piece_le_psi ⟨673,by decide +kernel⟩ t)
def piece0776 : AffinePiece := pieces[674]'(by decide +kernel)
theorem intervalAccepted0776 : candidateIntervalCheck candidate0776 (129/500) (259/1000) piece0776=true := by decide +kernel
noncomputable def cell0776 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0776 accepted0776 (129/500) (259/1000) piece0776
    intervalAccepted0776 (fun t => piece_le_psi ⟨674,by decide +kernel⟩ t)
def piece0777 : AffinePiece := pieces[675]'(by decide +kernel)
theorem intervalAccepted0777 : candidateIntervalCheck candidate0777 (259/1000) (13/50) piece0777=true := by decide +kernel
noncomputable def cell0777 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0777 accepted0777 (259/1000) (13/50) piece0777
    intervalAccepted0777 (fun t => piece_le_psi ⟨675,by decide +kernel⟩ t)
def piece0778 : AffinePiece := pieces[676]'(by decide +kernel)
theorem intervalAccepted0778 : candidateIntervalCheck candidate0778 (13/50) (261/1000) piece0778=true := by decide +kernel
noncomputable def cell0778 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0778 accepted0778 (13/50) (261/1000) piece0778
    intervalAccepted0778 (fun t => piece_le_psi ⟨676,by decide +kernel⟩ t)
def piece0779 : AffinePiece := pieces[677]'(by decide +kernel)
theorem intervalAccepted0779 : candidateIntervalCheck candidate0779 (261/1000) (131/500) piece0779=true := by decide +kernel
noncomputable def cell0779 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0779 accepted0779 (261/1000) (131/500) piece0779
    intervalAccepted0779 (fun t => piece_le_psi ⟨677,by decide +kernel⟩ t)
def piece0780 : AffinePiece := pieces[678]'(by decide +kernel)
theorem intervalAccepted0780 : candidateIntervalCheck candidate0780 (131/500) (263/1000) piece0780=true := by decide +kernel
noncomputable def cell0780 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0780 accepted0780 (131/500) (263/1000) piece0780
    intervalAccepted0780 (fun t => piece_le_psi ⟨678,by decide +kernel⟩ t)
def piece0781 : AffinePiece := pieces[679]'(by decide +kernel)
theorem intervalAccepted0781 : candidateIntervalCheck candidate0781 (263/1000) (33/125) piece0781=true := by decide +kernel
noncomputable def cell0781 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0781 accepted0781 (263/1000) (33/125) piece0781
    intervalAccepted0781 (fun t => piece_le_psi ⟨679,by decide +kernel⟩ t)
def piece0782 : AffinePiece := pieces[680]'(by decide +kernel)
theorem intervalAccepted0782 : candidateIntervalCheck candidate0782 (33/125) (53/200) piece0782=true := by decide +kernel
noncomputable def cell0782 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0782 accepted0782 (33/125) (53/200) piece0782
    intervalAccepted0782 (fun t => piece_le_psi ⟨680,by decide +kernel⟩ t)
def piece0783 : AffinePiece := pieces[681]'(by decide +kernel)
theorem intervalAccepted0783 : candidateIntervalCheck candidate0783 (53/200) (133/500) piece0783=true := by decide +kernel
noncomputable def cell0783 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0783 accepted0783 (53/200) (133/500) piece0783
    intervalAccepted0783 (fun t => piece_le_psi ⟨681,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0768, cell0769, cell0770, cell0771, cell0772, cell0773, cell0774, cell0775, cell0776, cell0777, cell0778, cell0779, cell0780, cell0781, cell0782, cell0783]
theorem chainAccepted : spinCellChainCheck (1/4) (133/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1/4) (133/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0048
