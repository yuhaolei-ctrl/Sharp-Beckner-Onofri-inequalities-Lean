module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0014

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0014
open CandidateBatch0014 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0224 : AffinePiece := pieces[184]'(by decide +kernel)
theorem intervalAccepted0224 : candidateIntervalCheck candidate0224 (1013/10000) (203/2000) piece0224=true := by decide +kernel
noncomputable def cell0224 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0224 accepted0224 (1013/10000) (203/2000) piece0224
    intervalAccepted0224 (fun t => piece_le_psi ⟨184,by decide +kernel⟩ t)
def piece0225 : AffinePiece := pieces[185]'(by decide +kernel)
theorem intervalAccepted0225 : candidateIntervalCheck candidate0225 (203/2000) (1017/10000) piece0225=true := by decide +kernel
noncomputable def cell0225 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0225 accepted0225 (203/2000) (1017/10000) piece0225
    intervalAccepted0225 (fun t => piece_le_psi ⟨185,by decide +kernel⟩ t)
def piece0226 : AffinePiece := pieces[186]'(by decide +kernel)
theorem intervalAccepted0226 : candidateIntervalCheck candidate0226 (1017/10000) (1019/10000) piece0226=true := by decide +kernel
noncomputable def cell0226 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0226 accepted0226 (1017/10000) (1019/10000) piece0226
    intervalAccepted0226 (fun t => piece_le_psi ⟨186,by decide +kernel⟩ t)
def piece0227 : AffinePiece := pieces[187]'(by decide +kernel)
theorem intervalAccepted0227 : candidateIntervalCheck candidate0227 (1019/10000) (1021/10000) piece0227=true := by decide +kernel
noncomputable def cell0227 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0227 accepted0227 (1019/10000) (1021/10000) piece0227
    intervalAccepted0227 (fun t => piece_le_psi ⟨187,by decide +kernel⟩ t)
def piece0228 : AffinePiece := pieces[188]'(by decide +kernel)
theorem intervalAccepted0228 : candidateIntervalCheck candidate0228 (1021/10000) (1023/10000) piece0228=true := by decide +kernel
noncomputable def cell0228 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0228 accepted0228 (1021/10000) (1023/10000) piece0228
    intervalAccepted0228 (fun t => piece_le_psi ⟨188,by decide +kernel⟩ t)
def piece0229 : AffinePiece := pieces[189]'(by decide +kernel)
theorem intervalAccepted0229 : candidateIntervalCheck candidate0229 (1023/10000) (41/400) piece0229=true := by decide +kernel
noncomputable def cell0229 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0229 accepted0229 (1023/10000) (41/400) piece0229
    intervalAccepted0229 (fun t => piece_le_psi ⟨189,by decide +kernel⟩ t)
def piece0230 : AffinePiece := pieces[190]'(by decide +kernel)
theorem intervalAccepted0230 : candidateIntervalCheck candidate0230 (41/400) (1027/10000) piece0230=true := by decide +kernel
noncomputable def cell0230 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0230 accepted0230 (41/400) (1027/10000) piece0230
    intervalAccepted0230 (fun t => piece_le_psi ⟨190,by decide +kernel⟩ t)
def piece0231 : AffinePiece := pieces[191]'(by decide +kernel)
theorem intervalAccepted0231 : candidateIntervalCheck candidate0231 (1027/10000) (1029/10000) piece0231=true := by decide +kernel
noncomputable def cell0231 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0231 accepted0231 (1027/10000) (1029/10000) piece0231
    intervalAccepted0231 (fun t => piece_le_psi ⟨191,by decide +kernel⟩ t)
def piece0232 : AffinePiece := pieces[192]'(by decide +kernel)
theorem intervalAccepted0232 : candidateIntervalCheck candidate0232 (1029/10000) (1031/10000) piece0232=true := by decide +kernel
noncomputable def cell0232 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0232 accepted0232 (1029/10000) (1031/10000) piece0232
    intervalAccepted0232 (fun t => piece_le_psi ⟨192,by decide +kernel⟩ t)
def piece0233 : AffinePiece := pieces[193]'(by decide +kernel)
theorem intervalAccepted0233 : candidateIntervalCheck candidate0233 (1031/10000) (1033/10000) piece0233=true := by decide +kernel
noncomputable def cell0233 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0233 accepted0233 (1031/10000) (1033/10000) piece0233
    intervalAccepted0233 (fun t => piece_le_psi ⟨193,by decide +kernel⟩ t)
def piece0234 : AffinePiece := pieces[194]'(by decide +kernel)
theorem intervalAccepted0234 : candidateIntervalCheck candidate0234 (1033/10000) (207/2000) piece0234=true := by decide +kernel
noncomputable def cell0234 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0234 accepted0234 (1033/10000) (207/2000) piece0234
    intervalAccepted0234 (fun t => piece_le_psi ⟨194,by decide +kernel⟩ t)
def piece0235 : AffinePiece := pieces[195]'(by decide +kernel)
theorem intervalAccepted0235 : candidateIntervalCheck candidate0235 (207/2000) (1037/10000) piece0235=true := by decide +kernel
noncomputable def cell0235 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0235 accepted0235 (207/2000) (1037/10000) piece0235
    intervalAccepted0235 (fun t => piece_le_psi ⟨195,by decide +kernel⟩ t)
def piece0236 : AffinePiece := pieces[196]'(by decide +kernel)
theorem intervalAccepted0236 : candidateIntervalCheck candidate0236 (1037/10000) (1039/10000) piece0236=true := by decide +kernel
noncomputable def cell0236 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0236 accepted0236 (1037/10000) (1039/10000) piece0236
    intervalAccepted0236 (fun t => piece_le_psi ⟨196,by decide +kernel⟩ t)
def piece0237 : AffinePiece := pieces[197]'(by decide +kernel)
theorem intervalAccepted0237 : candidateIntervalCheck candidate0237 (1039/10000) (1041/10000) piece0237=true := by decide +kernel
noncomputable def cell0237 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0237 accepted0237 (1039/10000) (1041/10000) piece0237
    intervalAccepted0237 (fun t => piece_le_psi ⟨197,by decide +kernel⟩ t)
def piece0238 : AffinePiece := pieces[198]'(by decide +kernel)
theorem intervalAccepted0238 : candidateIntervalCheck candidate0238 (1041/10000) (1043/10000) piece0238=true := by decide +kernel
noncomputable def cell0238 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0238 accepted0238 (1041/10000) (1043/10000) piece0238
    intervalAccepted0238 (fun t => piece_le_psi ⟨198,by decide +kernel⟩ t)
def piece0239 : AffinePiece := pieces[199]'(by decide +kernel)
theorem intervalAccepted0239 : candidateIntervalCheck candidate0239 (1043/10000) (209/2000) piece0239=true := by decide +kernel
noncomputable def cell0239 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0239 accepted0239 (1043/10000) (209/2000) piece0239
    intervalAccepted0239 (fun t => piece_le_psi ⟨199,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0224, cell0225, cell0226, cell0227, cell0228, cell0229, cell0230, cell0231, cell0232, cell0233, cell0234, cell0235, cell0236, cell0237, cell0238, cell0239]
theorem chainAccepted : spinCellChainCheck (1013/10000) (209/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1013/10000) (209/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0014
