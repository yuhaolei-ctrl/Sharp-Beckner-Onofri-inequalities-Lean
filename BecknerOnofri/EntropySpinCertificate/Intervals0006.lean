import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0006
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0006
open CandidateBatch0006 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0096 : AffinePiece := pieces[56]'(by decide +kernel)
theorem intervalAccepted0096 : candidateIntervalCheck candidate0096 (757/10000) (759/10000) piece0096=true := by decide +kernel
noncomputable def cell0096 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0096 accepted0096 (757/10000) (759/10000) piece0096
    intervalAccepted0096 (fun t => piece_le_psi ⟨56,by decide +kernel⟩ t)
def piece0097 : AffinePiece := pieces[57]'(by decide +kernel)
theorem intervalAccepted0097 : candidateIntervalCheck candidate0097 (759/10000) (761/10000) piece0097=true := by decide +kernel
noncomputable def cell0097 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0097 accepted0097 (759/10000) (761/10000) piece0097
    intervalAccepted0097 (fun t => piece_le_psi ⟨57,by decide +kernel⟩ t)
def piece0098 : AffinePiece := pieces[58]'(by decide +kernel)
theorem intervalAccepted0098 : candidateIntervalCheck candidate0098 (761/10000) (763/10000) piece0098=true := by decide +kernel
noncomputable def cell0098 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0098 accepted0098 (761/10000) (763/10000) piece0098
    intervalAccepted0098 (fun t => piece_le_psi ⟨58,by decide +kernel⟩ t)
def piece0099 : AffinePiece := pieces[59]'(by decide +kernel)
theorem intervalAccepted0099 : candidateIntervalCheck candidate0099 (763/10000) (153/2000) piece0099=true := by decide +kernel
noncomputable def cell0099 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0099 accepted0099 (763/10000) (153/2000) piece0099
    intervalAccepted0099 (fun t => piece_le_psi ⟨59,by decide +kernel⟩ t)
def piece0100 : AffinePiece := pieces[60]'(by decide +kernel)
theorem intervalAccepted0100 : candidateIntervalCheck candidate0100 (153/2000) (767/10000) piece0100=true := by decide +kernel
noncomputable def cell0100 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0100 accepted0100 (153/2000) (767/10000) piece0100
    intervalAccepted0100 (fun t => piece_le_psi ⟨60,by decide +kernel⟩ t)
def piece0101 : AffinePiece := pieces[61]'(by decide +kernel)
theorem intervalAccepted0101 : candidateIntervalCheck candidate0101 (767/10000) (769/10000) piece0101=true := by decide +kernel
noncomputable def cell0101 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0101 accepted0101 (767/10000) (769/10000) piece0101
    intervalAccepted0101 (fun t => piece_le_psi ⟨61,by decide +kernel⟩ t)
def piece0102 : AffinePiece := pieces[62]'(by decide +kernel)
theorem intervalAccepted0102 : candidateIntervalCheck candidate0102 (769/10000) (771/10000) piece0102=true := by decide +kernel
noncomputable def cell0102 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0102 accepted0102 (769/10000) (771/10000) piece0102
    intervalAccepted0102 (fun t => piece_le_psi ⟨62,by decide +kernel⟩ t)
def piece0103 : AffinePiece := pieces[63]'(by decide +kernel)
theorem intervalAccepted0103 : candidateIntervalCheck candidate0103 (771/10000) (773/10000) piece0103=true := by decide +kernel
noncomputable def cell0103 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0103 accepted0103 (771/10000) (773/10000) piece0103
    intervalAccepted0103 (fun t => piece_le_psi ⟨63,by decide +kernel⟩ t)
def piece0104 : AffinePiece := pieces[64]'(by decide +kernel)
theorem intervalAccepted0104 : candidateIntervalCheck candidate0104 (773/10000) (31/400) piece0104=true := by decide +kernel
noncomputable def cell0104 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0104 accepted0104 (773/10000) (31/400) piece0104
    intervalAccepted0104 (fun t => piece_le_psi ⟨64,by decide +kernel⟩ t)
def piece0105 : AffinePiece := pieces[65]'(by decide +kernel)
theorem intervalAccepted0105 : candidateIntervalCheck candidate0105 (31/400) (777/10000) piece0105=true := by decide +kernel
noncomputable def cell0105 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0105 accepted0105 (31/400) (777/10000) piece0105
    intervalAccepted0105 (fun t => piece_le_psi ⟨65,by decide +kernel⟩ t)
def piece0106 : AffinePiece := pieces[66]'(by decide +kernel)
theorem intervalAccepted0106 : candidateIntervalCheck candidate0106 (777/10000) (779/10000) piece0106=true := by decide +kernel
noncomputable def cell0106 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0106 accepted0106 (777/10000) (779/10000) piece0106
    intervalAccepted0106 (fun t => piece_le_psi ⟨66,by decide +kernel⟩ t)
def piece0107 : AffinePiece := pieces[67]'(by decide +kernel)
theorem intervalAccepted0107 : candidateIntervalCheck candidate0107 (779/10000) (781/10000) piece0107=true := by decide +kernel
noncomputable def cell0107 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0107 accepted0107 (779/10000) (781/10000) piece0107
    intervalAccepted0107 (fun t => piece_le_psi ⟨67,by decide +kernel⟩ t)
def piece0108 : AffinePiece := pieces[68]'(by decide +kernel)
theorem intervalAccepted0108 : candidateIntervalCheck candidate0108 (781/10000) (783/10000) piece0108=true := by decide +kernel
noncomputable def cell0108 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0108 accepted0108 (781/10000) (783/10000) piece0108
    intervalAccepted0108 (fun t => piece_le_psi ⟨68,by decide +kernel⟩ t)
def piece0109 : AffinePiece := pieces[69]'(by decide +kernel)
theorem intervalAccepted0109 : candidateIntervalCheck candidate0109 (783/10000) (157/2000) piece0109=true := by decide +kernel
noncomputable def cell0109 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0109 accepted0109 (783/10000) (157/2000) piece0109
    intervalAccepted0109 (fun t => piece_le_psi ⟨69,by decide +kernel⟩ t)
def piece0110 : AffinePiece := pieces[70]'(by decide +kernel)
theorem intervalAccepted0110 : candidateIntervalCheck candidate0110 (157/2000) (787/10000) piece0110=true := by decide +kernel
noncomputable def cell0110 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0110 accepted0110 (157/2000) (787/10000) piece0110
    intervalAccepted0110 (fun t => piece_le_psi ⟨70,by decide +kernel⟩ t)
def piece0111 : AffinePiece := pieces[71]'(by decide +kernel)
theorem intervalAccepted0111 : candidateIntervalCheck candidate0111 (787/10000) (789/10000) piece0111=true := by decide +kernel
noncomputable def cell0111 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0111 accepted0111 (787/10000) (789/10000) piece0111
    intervalAccepted0111 (fun t => piece_le_psi ⟨71,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0096, cell0097, cell0098, cell0099, cell0100, cell0101, cell0102, cell0103, cell0104, cell0105, cell0106, cell0107, cell0108, cell0109, cell0110, cell0111]
theorem chainAccepted : spinCellChainCheck (757/10000) (789/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (757/10000) (789/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0006
