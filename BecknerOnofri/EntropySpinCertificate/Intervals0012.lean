import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0012
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0012
open CandidateBatch0012 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0192 : AffinePiece := pieces[152]'(by decide +kernel)
theorem intervalAccepted0192 : candidateIntervalCheck candidate0192 (949/10000) (951/10000) piece0192=true := by decide +kernel
noncomputable def cell0192 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0192 accepted0192 (949/10000) (951/10000) piece0192
    intervalAccepted0192 (fun t => piece_le_psi ⟨152,by decide +kernel⟩ t)
def piece0193 : AffinePiece := pieces[153]'(by decide +kernel)
theorem intervalAccepted0193 : candidateIntervalCheck candidate0193 (951/10000) (953/10000) piece0193=true := by decide +kernel
noncomputable def cell0193 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0193 accepted0193 (951/10000) (953/10000) piece0193
    intervalAccepted0193 (fun t => piece_le_psi ⟨153,by decide +kernel⟩ t)
def piece0194 : AffinePiece := pieces[154]'(by decide +kernel)
theorem intervalAccepted0194 : candidateIntervalCheck candidate0194 (953/10000) (191/2000) piece0194=true := by decide +kernel
noncomputable def cell0194 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0194 accepted0194 (953/10000) (191/2000) piece0194
    intervalAccepted0194 (fun t => piece_le_psi ⟨154,by decide +kernel⟩ t)
def piece0195 : AffinePiece := pieces[155]'(by decide +kernel)
theorem intervalAccepted0195 : candidateIntervalCheck candidate0195 (191/2000) (957/10000) piece0195=true := by decide +kernel
noncomputable def cell0195 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0195 accepted0195 (191/2000) (957/10000) piece0195
    intervalAccepted0195 (fun t => piece_le_psi ⟨155,by decide +kernel⟩ t)
def piece0196 : AffinePiece := pieces[156]'(by decide +kernel)
theorem intervalAccepted0196 : candidateIntervalCheck candidate0196 (957/10000) (959/10000) piece0196=true := by decide +kernel
noncomputable def cell0196 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0196 accepted0196 (957/10000) (959/10000) piece0196
    intervalAccepted0196 (fun t => piece_le_psi ⟨156,by decide +kernel⟩ t)
def piece0197 : AffinePiece := pieces[157]'(by decide +kernel)
theorem intervalAccepted0197 : candidateIntervalCheck candidate0197 (959/10000) (961/10000) piece0197=true := by decide +kernel
noncomputable def cell0197 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0197 accepted0197 (959/10000) (961/10000) piece0197
    intervalAccepted0197 (fun t => piece_le_psi ⟨157,by decide +kernel⟩ t)
def piece0198 : AffinePiece := pieces[158]'(by decide +kernel)
theorem intervalAccepted0198 : candidateIntervalCheck candidate0198 (961/10000) (963/10000) piece0198=true := by decide +kernel
noncomputable def cell0198 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0198 accepted0198 (961/10000) (963/10000) piece0198
    intervalAccepted0198 (fun t => piece_le_psi ⟨158,by decide +kernel⟩ t)
def piece0199 : AffinePiece := pieces[159]'(by decide +kernel)
theorem intervalAccepted0199 : candidateIntervalCheck candidate0199 (963/10000) (193/2000) piece0199=true := by decide +kernel
noncomputable def cell0199 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0199 accepted0199 (963/10000) (193/2000) piece0199
    intervalAccepted0199 (fun t => piece_le_psi ⟨159,by decide +kernel⟩ t)
def piece0200 : AffinePiece := pieces[160]'(by decide +kernel)
theorem intervalAccepted0200 : candidateIntervalCheck candidate0200 (193/2000) (967/10000) piece0200=true := by decide +kernel
noncomputable def cell0200 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0200 accepted0200 (193/2000) (967/10000) piece0200
    intervalAccepted0200 (fun t => piece_le_psi ⟨160,by decide +kernel⟩ t)
def piece0201 : AffinePiece := pieces[161]'(by decide +kernel)
theorem intervalAccepted0201 : candidateIntervalCheck candidate0201 (967/10000) (969/10000) piece0201=true := by decide +kernel
noncomputable def cell0201 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0201 accepted0201 (967/10000) (969/10000) piece0201
    intervalAccepted0201 (fun t => piece_le_psi ⟨161,by decide +kernel⟩ t)
def piece0202 : AffinePiece := pieces[162]'(by decide +kernel)
theorem intervalAccepted0202 : candidateIntervalCheck candidate0202 (969/10000) (971/10000) piece0202=true := by decide +kernel
noncomputable def cell0202 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0202 accepted0202 (969/10000) (971/10000) piece0202
    intervalAccepted0202 (fun t => piece_le_psi ⟨162,by decide +kernel⟩ t)
def piece0203 : AffinePiece := pieces[163]'(by decide +kernel)
theorem intervalAccepted0203 : candidateIntervalCheck candidate0203 (971/10000) (973/10000) piece0203=true := by decide +kernel
noncomputable def cell0203 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0203 accepted0203 (971/10000) (973/10000) piece0203
    intervalAccepted0203 (fun t => piece_le_psi ⟨163,by decide +kernel⟩ t)
def piece0204 : AffinePiece := pieces[164]'(by decide +kernel)
theorem intervalAccepted0204 : candidateIntervalCheck candidate0204 (973/10000) (39/400) piece0204=true := by decide +kernel
noncomputable def cell0204 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0204 accepted0204 (973/10000) (39/400) piece0204
    intervalAccepted0204 (fun t => piece_le_psi ⟨164,by decide +kernel⟩ t)
def piece0205 : AffinePiece := pieces[165]'(by decide +kernel)
theorem intervalAccepted0205 : candidateIntervalCheck candidate0205 (39/400) (977/10000) piece0205=true := by decide +kernel
noncomputable def cell0205 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0205 accepted0205 (39/400) (977/10000) piece0205
    intervalAccepted0205 (fun t => piece_le_psi ⟨165,by decide +kernel⟩ t)
def piece0206 : AffinePiece := pieces[166]'(by decide +kernel)
theorem intervalAccepted0206 : candidateIntervalCheck candidate0206 (977/10000) (979/10000) piece0206=true := by decide +kernel
noncomputable def cell0206 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0206 accepted0206 (977/10000) (979/10000) piece0206
    intervalAccepted0206 (fun t => piece_le_psi ⟨166,by decide +kernel⟩ t)
def piece0207 : AffinePiece := pieces[167]'(by decide +kernel)
theorem intervalAccepted0207 : candidateIntervalCheck candidate0207 (979/10000) (981/10000) piece0207=true := by decide +kernel
noncomputable def cell0207 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0207 accepted0207 (979/10000) (981/10000) piece0207
    intervalAccepted0207 (fun t => piece_le_psi ⟨167,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0192, cell0193, cell0194, cell0195, cell0196, cell0197, cell0198, cell0199, cell0200, cell0201, cell0202, cell0203, cell0204, cell0205, cell0206, cell0207]
theorem chainAccepted : spinCellChainCheck (949/10000) (981/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (949/10000) (981/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0012
