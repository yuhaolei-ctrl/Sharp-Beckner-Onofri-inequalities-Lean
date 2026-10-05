import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0007
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0007
open CandidateBatch0007 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0112 : AffinePiece := pieces[72]'(by decide +kernel)
theorem intervalAccepted0112 : candidateIntervalCheck candidate0112 (789/10000) (791/10000) piece0112=true := by decide +kernel
noncomputable def cell0112 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0112 accepted0112 (789/10000) (791/10000) piece0112
    intervalAccepted0112 (fun t => piece_le_psi ⟨72,by decide +kernel⟩ t)
def piece0113 : AffinePiece := pieces[73]'(by decide +kernel)
theorem intervalAccepted0113 : candidateIntervalCheck candidate0113 (791/10000) (793/10000) piece0113=true := by decide +kernel
noncomputable def cell0113 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0113 accepted0113 (791/10000) (793/10000) piece0113
    intervalAccepted0113 (fun t => piece_le_psi ⟨73,by decide +kernel⟩ t)
def piece0114 : AffinePiece := pieces[74]'(by decide +kernel)
theorem intervalAccepted0114 : candidateIntervalCheck candidate0114 (793/10000) (159/2000) piece0114=true := by decide +kernel
noncomputable def cell0114 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0114 accepted0114 (793/10000) (159/2000) piece0114
    intervalAccepted0114 (fun t => piece_le_psi ⟨74,by decide +kernel⟩ t)
def piece0115 : AffinePiece := pieces[75]'(by decide +kernel)
theorem intervalAccepted0115 : candidateIntervalCheck candidate0115 (159/2000) (797/10000) piece0115=true := by decide +kernel
noncomputable def cell0115 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0115 accepted0115 (159/2000) (797/10000) piece0115
    intervalAccepted0115 (fun t => piece_le_psi ⟨75,by decide +kernel⟩ t)
def piece0116 : AffinePiece := pieces[76]'(by decide +kernel)
theorem intervalAccepted0116 : candidateIntervalCheck candidate0116 (797/10000) (799/10000) piece0116=true := by decide +kernel
noncomputable def cell0116 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0116 accepted0116 (797/10000) (799/10000) piece0116
    intervalAccepted0116 (fun t => piece_le_psi ⟨76,by decide +kernel⟩ t)
def piece0117 : AffinePiece := pieces[77]'(by decide +kernel)
theorem intervalAccepted0117 : candidateIntervalCheck candidate0117 (799/10000) (801/10000) piece0117=true := by decide +kernel
noncomputable def cell0117 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0117 accepted0117 (799/10000) (801/10000) piece0117
    intervalAccepted0117 (fun t => piece_le_psi ⟨77,by decide +kernel⟩ t)
def piece0118 : AffinePiece := pieces[78]'(by decide +kernel)
theorem intervalAccepted0118 : candidateIntervalCheck candidate0118 (801/10000) (803/10000) piece0118=true := by decide +kernel
noncomputable def cell0118 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0118 accepted0118 (801/10000) (803/10000) piece0118
    intervalAccepted0118 (fun t => piece_le_psi ⟨78,by decide +kernel⟩ t)
def piece0119 : AffinePiece := pieces[79]'(by decide +kernel)
theorem intervalAccepted0119 : candidateIntervalCheck candidate0119 (803/10000) (161/2000) piece0119=true := by decide +kernel
noncomputable def cell0119 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0119 accepted0119 (803/10000) (161/2000) piece0119
    intervalAccepted0119 (fun t => piece_le_psi ⟨79,by decide +kernel⟩ t)
def piece0120 : AffinePiece := pieces[80]'(by decide +kernel)
theorem intervalAccepted0120 : candidateIntervalCheck candidate0120 (161/2000) (807/10000) piece0120=true := by decide +kernel
noncomputable def cell0120 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0120 accepted0120 (161/2000) (807/10000) piece0120
    intervalAccepted0120 (fun t => piece_le_psi ⟨80,by decide +kernel⟩ t)
def piece0121 : AffinePiece := pieces[81]'(by decide +kernel)
theorem intervalAccepted0121 : candidateIntervalCheck candidate0121 (807/10000) (809/10000) piece0121=true := by decide +kernel
noncomputable def cell0121 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0121 accepted0121 (807/10000) (809/10000) piece0121
    intervalAccepted0121 (fun t => piece_le_psi ⟨81,by decide +kernel⟩ t)
def piece0122 : AffinePiece := pieces[82]'(by decide +kernel)
theorem intervalAccepted0122 : candidateIntervalCheck candidate0122 (809/10000) (811/10000) piece0122=true := by decide +kernel
noncomputable def cell0122 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0122 accepted0122 (809/10000) (811/10000) piece0122
    intervalAccepted0122 (fun t => piece_le_psi ⟨82,by decide +kernel⟩ t)
def piece0123 : AffinePiece := pieces[83]'(by decide +kernel)
theorem intervalAccepted0123 : candidateIntervalCheck candidate0123 (811/10000) (813/10000) piece0123=true := by decide +kernel
noncomputable def cell0123 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0123 accepted0123 (811/10000) (813/10000) piece0123
    intervalAccepted0123 (fun t => piece_le_psi ⟨83,by decide +kernel⟩ t)
def piece0124 : AffinePiece := pieces[84]'(by decide +kernel)
theorem intervalAccepted0124 : candidateIntervalCheck candidate0124 (813/10000) (163/2000) piece0124=true := by decide +kernel
noncomputable def cell0124 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0124 accepted0124 (813/10000) (163/2000) piece0124
    intervalAccepted0124 (fun t => piece_le_psi ⟨84,by decide +kernel⟩ t)
def piece0125 : AffinePiece := pieces[85]'(by decide +kernel)
theorem intervalAccepted0125 : candidateIntervalCheck candidate0125 (163/2000) (817/10000) piece0125=true := by decide +kernel
noncomputable def cell0125 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0125 accepted0125 (163/2000) (817/10000) piece0125
    intervalAccepted0125 (fun t => piece_le_psi ⟨85,by decide +kernel⟩ t)
def piece0126 : AffinePiece := pieces[86]'(by decide +kernel)
theorem intervalAccepted0126 : candidateIntervalCheck candidate0126 (817/10000) (819/10000) piece0126=true := by decide +kernel
noncomputable def cell0126 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0126 accepted0126 (817/10000) (819/10000) piece0126
    intervalAccepted0126 (fun t => piece_le_psi ⟨86,by decide +kernel⟩ t)
def piece0127 : AffinePiece := pieces[87]'(by decide +kernel)
theorem intervalAccepted0127 : candidateIntervalCheck candidate0127 (819/10000) (821/10000) piece0127=true := by decide +kernel
noncomputable def cell0127 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0127 accepted0127 (819/10000) (821/10000) piece0127
    intervalAccepted0127 (fun t => piece_le_psi ⟨87,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0112, cell0113, cell0114, cell0115, cell0116, cell0117, cell0118, cell0119, cell0120, cell0121, cell0122, cell0123, cell0124, cell0125, cell0126, cell0127]
theorem chainAccepted : spinCellChainCheck (789/10000) (821/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (789/10000) (821/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0007
