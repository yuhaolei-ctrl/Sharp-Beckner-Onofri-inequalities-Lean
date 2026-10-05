module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0051

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0051
open CandidateBatch0051 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0816 : AffinePiece := pieces[714]'(by decide +kernel)
theorem intervalAccepted0816 : candidateIntervalCheck candidate0816 (149/500) (299/1000) piece0816=true := by decide +kernel
noncomputable def cell0816 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0816 accepted0816 (149/500) (299/1000) piece0816
    intervalAccepted0816 (fun t => piece_le_psi ⟨714,by decide +kernel⟩ t)
def piece0817 : AffinePiece := pieces[715]'(by decide +kernel)
theorem intervalAccepted0817 : candidateIntervalCheck candidate0817 (299/1000) (3/10) piece0817=true := by decide +kernel
noncomputable def cell0817 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0817 accepted0817 (299/1000) (3/10) piece0817
    intervalAccepted0817 (fun t => piece_le_psi ⟨715,by decide +kernel⟩ t)
def piece0818 : AffinePiece := pieces[716]'(by decide +kernel)
theorem intervalAccepted0818 : candidateIntervalCheck candidate0818 (3/10) (301/1000) piece0818=true := by decide +kernel
noncomputable def cell0818 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0818 accepted0818 (3/10) (301/1000) piece0818
    intervalAccepted0818 (fun t => piece_le_psi ⟨716,by decide +kernel⟩ t)
def piece0819 : AffinePiece := pieces[717]'(by decide +kernel)
theorem intervalAccepted0819 : candidateIntervalCheck candidate0819 (301/1000) (151/500) piece0819=true := by decide +kernel
noncomputable def cell0819 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0819 accepted0819 (301/1000) (151/500) piece0819
    intervalAccepted0819 (fun t => piece_le_psi ⟨717,by decide +kernel⟩ t)
def piece0820 : AffinePiece := pieces[718]'(by decide +kernel)
theorem intervalAccepted0820 : candidateIntervalCheck candidate0820 (151/500) (303/1000) piece0820=true := by decide +kernel
noncomputable def cell0820 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0820 accepted0820 (151/500) (303/1000) piece0820
    intervalAccepted0820 (fun t => piece_le_psi ⟨718,by decide +kernel⟩ t)
def piece0821 : AffinePiece := pieces[719]'(by decide +kernel)
theorem intervalAccepted0821 : candidateIntervalCheck candidate0821 (303/1000) (38/125) piece0821=true := by decide +kernel
noncomputable def cell0821 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0821 accepted0821 (303/1000) (38/125) piece0821
    intervalAccepted0821 (fun t => piece_le_psi ⟨719,by decide +kernel⟩ t)
def piece0822 : AffinePiece := pieces[720]'(by decide +kernel)
theorem intervalAccepted0822 : candidateIntervalCheck candidate0822 (38/125) (61/200) piece0822=true := by decide +kernel
noncomputable def cell0822 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0822 accepted0822 (38/125) (61/200) piece0822
    intervalAccepted0822 (fun t => piece_le_psi ⟨720,by decide +kernel⟩ t)
def piece0823 : AffinePiece := pieces[721]'(by decide +kernel)
theorem intervalAccepted0823 : candidateIntervalCheck candidate0823 (61/200) (153/500) piece0823=true := by decide +kernel
noncomputable def cell0823 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0823 accepted0823 (61/200) (153/500) piece0823
    intervalAccepted0823 (fun t => piece_le_psi ⟨721,by decide +kernel⟩ t)
def piece0824 : AffinePiece := pieces[722]'(by decide +kernel)
theorem intervalAccepted0824 : candidateIntervalCheck candidate0824 (153/500) (307/1000) piece0824=true := by decide +kernel
noncomputable def cell0824 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0824 accepted0824 (153/500) (307/1000) piece0824
    intervalAccepted0824 (fun t => piece_le_psi ⟨722,by decide +kernel⟩ t)
def piece0825 : AffinePiece := pieces[723]'(by decide +kernel)
theorem intervalAccepted0825 : candidateIntervalCheck candidate0825 (307/1000) (77/250) piece0825=true := by decide +kernel
noncomputable def cell0825 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0825 accepted0825 (307/1000) (77/250) piece0825
    intervalAccepted0825 (fun t => piece_le_psi ⟨723,by decide +kernel⟩ t)
def piece0826 : AffinePiece := pieces[724]'(by decide +kernel)
theorem intervalAccepted0826 : candidateIntervalCheck candidate0826 (77/250) (309/1000) piece0826=true := by decide +kernel
noncomputable def cell0826 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0826 accepted0826 (77/250) (309/1000) piece0826
    intervalAccepted0826 (fun t => piece_le_psi ⟨724,by decide +kernel⟩ t)
def piece0827 : AffinePiece := pieces[725]'(by decide +kernel)
theorem intervalAccepted0827 : candidateIntervalCheck candidate0827 (309/1000) (31/100) piece0827=true := by decide +kernel
noncomputable def cell0827 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0827 accepted0827 (309/1000) (31/100) piece0827
    intervalAccepted0827 (fun t => piece_le_psi ⟨725,by decide +kernel⟩ t)
def piece0828 : AffinePiece := pieces[726]'(by decide +kernel)
theorem intervalAccepted0828 : candidateIntervalCheck candidate0828 (31/100) (311/1000) piece0828=true := by decide +kernel
noncomputable def cell0828 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0828 accepted0828 (31/100) (311/1000) piece0828
    intervalAccepted0828 (fun t => piece_le_psi ⟨726,by decide +kernel⟩ t)
def piece0829 : AffinePiece := pieces[727]'(by decide +kernel)
theorem intervalAccepted0829 : candidateIntervalCheck candidate0829 (311/1000) (39/125) piece0829=true := by decide +kernel
noncomputable def cell0829 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0829 accepted0829 (311/1000) (39/125) piece0829
    intervalAccepted0829 (fun t => piece_le_psi ⟨727,by decide +kernel⟩ t)
def piece0830 : AffinePiece := pieces[728]'(by decide +kernel)
theorem intervalAccepted0830 : candidateIntervalCheck candidate0830 (39/125) (313/1000) piece0830=true := by decide +kernel
noncomputable def cell0830 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0830 accepted0830 (39/125) (313/1000) piece0830
    intervalAccepted0830 (fun t => piece_le_psi ⟨728,by decide +kernel⟩ t)
def piece0831 : AffinePiece := pieces[729]'(by decide +kernel)
theorem intervalAccepted0831 : candidateIntervalCheck candidate0831 (313/1000) (157/500) piece0831=true := by decide +kernel
noncomputable def cell0831 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0831 accepted0831 (313/1000) (157/500) piece0831
    intervalAccepted0831 (fun t => piece_le_psi ⟨729,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0816, cell0817, cell0818, cell0819, cell0820, cell0821, cell0822, cell0823, cell0824, cell0825, cell0826, cell0827, cell0828, cell0829, cell0830, cell0831]
theorem chainAccepted : spinCellChainCheck (149/500) (157/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (149/500) (157/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0051
