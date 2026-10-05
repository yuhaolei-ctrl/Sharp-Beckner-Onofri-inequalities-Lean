import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0050
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0050
open CandidateBatch0050 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0800 : AffinePiece := pieces[698]'(by decide +kernel)
theorem intervalAccepted0800 : candidateIntervalCheck candidate0800 (141/500) (283/1000) piece0800=true := by decide +kernel
noncomputable def cell0800 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0800 accepted0800 (141/500) (283/1000) piece0800
    intervalAccepted0800 (fun t => piece_le_psi ⟨698,by decide +kernel⟩ t)
def piece0801 : AffinePiece := pieces[699]'(by decide +kernel)
theorem intervalAccepted0801 : candidateIntervalCheck candidate0801 (283/1000) (71/250) piece0801=true := by decide +kernel
noncomputable def cell0801 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0801 accepted0801 (283/1000) (71/250) piece0801
    intervalAccepted0801 (fun t => piece_le_psi ⟨699,by decide +kernel⟩ t)
def piece0802 : AffinePiece := pieces[700]'(by decide +kernel)
theorem intervalAccepted0802 : candidateIntervalCheck candidate0802 (71/250) (57/200) piece0802=true := by decide +kernel
noncomputable def cell0802 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0802 accepted0802 (71/250) (57/200) piece0802
    intervalAccepted0802 (fun t => piece_le_psi ⟨700,by decide +kernel⟩ t)
def piece0803 : AffinePiece := pieces[701]'(by decide +kernel)
theorem intervalAccepted0803 : candidateIntervalCheck candidate0803 (57/200) (143/500) piece0803=true := by decide +kernel
noncomputable def cell0803 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0803 accepted0803 (57/200) (143/500) piece0803
    intervalAccepted0803 (fun t => piece_le_psi ⟨701,by decide +kernel⟩ t)
def piece0804 : AffinePiece := pieces[702]'(by decide +kernel)
theorem intervalAccepted0804 : candidateIntervalCheck candidate0804 (143/500) (287/1000) piece0804=true := by decide +kernel
noncomputable def cell0804 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0804 accepted0804 (143/500) (287/1000) piece0804
    intervalAccepted0804 (fun t => piece_le_psi ⟨702,by decide +kernel⟩ t)
def piece0805 : AffinePiece := pieces[703]'(by decide +kernel)
theorem intervalAccepted0805 : candidateIntervalCheck candidate0805 (287/1000) (36/125) piece0805=true := by decide +kernel
noncomputable def cell0805 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0805 accepted0805 (287/1000) (36/125) piece0805
    intervalAccepted0805 (fun t => piece_le_psi ⟨703,by decide +kernel⟩ t)
def piece0806 : AffinePiece := pieces[704]'(by decide +kernel)
theorem intervalAccepted0806 : candidateIntervalCheck candidate0806 (36/125) (289/1000) piece0806=true := by decide +kernel
noncomputable def cell0806 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0806 accepted0806 (36/125) (289/1000) piece0806
    intervalAccepted0806 (fun t => piece_le_psi ⟨704,by decide +kernel⟩ t)
def piece0807 : AffinePiece := pieces[705]'(by decide +kernel)
theorem intervalAccepted0807 : candidateIntervalCheck candidate0807 (289/1000) (29/100) piece0807=true := by decide +kernel
noncomputable def cell0807 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0807 accepted0807 (289/1000) (29/100) piece0807
    intervalAccepted0807 (fun t => piece_le_psi ⟨705,by decide +kernel⟩ t)
def piece0808 : AffinePiece := pieces[706]'(by decide +kernel)
theorem intervalAccepted0808 : candidateIntervalCheck candidate0808 (29/100) (291/1000) piece0808=true := by decide +kernel
noncomputable def cell0808 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0808 accepted0808 (29/100) (291/1000) piece0808
    intervalAccepted0808 (fun t => piece_le_psi ⟨706,by decide +kernel⟩ t)
def piece0809 : AffinePiece := pieces[707]'(by decide +kernel)
theorem intervalAccepted0809 : candidateIntervalCheck candidate0809 (291/1000) (73/250) piece0809=true := by decide +kernel
noncomputable def cell0809 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0809 accepted0809 (291/1000) (73/250) piece0809
    intervalAccepted0809 (fun t => piece_le_psi ⟨707,by decide +kernel⟩ t)
def piece0810 : AffinePiece := pieces[708]'(by decide +kernel)
theorem intervalAccepted0810 : candidateIntervalCheck candidate0810 (73/250) (293/1000) piece0810=true := by decide +kernel
noncomputable def cell0810 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0810 accepted0810 (73/250) (293/1000) piece0810
    intervalAccepted0810 (fun t => piece_le_psi ⟨708,by decide +kernel⟩ t)
def piece0811 : AffinePiece := pieces[709]'(by decide +kernel)
theorem intervalAccepted0811 : candidateIntervalCheck candidate0811 (293/1000) (147/500) piece0811=true := by decide +kernel
noncomputable def cell0811 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0811 accepted0811 (293/1000) (147/500) piece0811
    intervalAccepted0811 (fun t => piece_le_psi ⟨709,by decide +kernel⟩ t)
def piece0812 : AffinePiece := pieces[710]'(by decide +kernel)
theorem intervalAccepted0812 : candidateIntervalCheck candidate0812 (147/500) (59/200) piece0812=true := by decide +kernel
noncomputable def cell0812 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0812 accepted0812 (147/500) (59/200) piece0812
    intervalAccepted0812 (fun t => piece_le_psi ⟨710,by decide +kernel⟩ t)
def piece0813 : AffinePiece := pieces[711]'(by decide +kernel)
theorem intervalAccepted0813 : candidateIntervalCheck candidate0813 (59/200) (37/125) piece0813=true := by decide +kernel
noncomputable def cell0813 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0813 accepted0813 (59/200) (37/125) piece0813
    intervalAccepted0813 (fun t => piece_le_psi ⟨711,by decide +kernel⟩ t)
def piece0814 : AffinePiece := pieces[712]'(by decide +kernel)
theorem intervalAccepted0814 : candidateIntervalCheck candidate0814 (37/125) (297/1000) piece0814=true := by decide +kernel
noncomputable def cell0814 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0814 accepted0814 (37/125) (297/1000) piece0814
    intervalAccepted0814 (fun t => piece_le_psi ⟨712,by decide +kernel⟩ t)
def piece0815 : AffinePiece := pieces[713]'(by decide +kernel)
theorem intervalAccepted0815 : candidateIntervalCheck candidate0815 (297/1000) (149/500) piece0815=true := by decide +kernel
noncomputable def cell0815 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0815 accepted0815 (297/1000) (149/500) piece0815
    intervalAccepted0815 (fun t => piece_le_psi ⟨713,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0800, cell0801, cell0802, cell0803, cell0804, cell0805, cell0806, cell0807, cell0808, cell0809, cell0810, cell0811, cell0812, cell0813, cell0814, cell0815]
theorem chainAccepted : spinCellChainCheck (141/500) (149/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (141/500) (149/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0050
