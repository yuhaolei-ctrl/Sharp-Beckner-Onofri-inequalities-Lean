module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0013

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0013
open CandidateBatch0013 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0208 : AffinePiece := pieces[168]'(by decide +kernel)
theorem intervalAccepted0208 : candidateIntervalCheck candidate0208 (981/10000) (983/10000) piece0208=true := by decide +kernel
noncomputable def cell0208 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0208 accepted0208 (981/10000) (983/10000) piece0208
    intervalAccepted0208 (fun t => piece_le_psi ⟨168,by decide +kernel⟩ t)
def piece0209 : AffinePiece := pieces[169]'(by decide +kernel)
theorem intervalAccepted0209 : candidateIntervalCheck candidate0209 (983/10000) (197/2000) piece0209=true := by decide +kernel
noncomputable def cell0209 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0209 accepted0209 (983/10000) (197/2000) piece0209
    intervalAccepted0209 (fun t => piece_le_psi ⟨169,by decide +kernel⟩ t)
def piece0210 : AffinePiece := pieces[170]'(by decide +kernel)
theorem intervalAccepted0210 : candidateIntervalCheck candidate0210 (197/2000) (987/10000) piece0210=true := by decide +kernel
noncomputable def cell0210 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0210 accepted0210 (197/2000) (987/10000) piece0210
    intervalAccepted0210 (fun t => piece_le_psi ⟨170,by decide +kernel⟩ t)
def piece0211 : AffinePiece := pieces[171]'(by decide +kernel)
theorem intervalAccepted0211 : candidateIntervalCheck candidate0211 (987/10000) (989/10000) piece0211=true := by decide +kernel
noncomputable def cell0211 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0211 accepted0211 (987/10000) (989/10000) piece0211
    intervalAccepted0211 (fun t => piece_le_psi ⟨171,by decide +kernel⟩ t)
def piece0212 : AffinePiece := pieces[172]'(by decide +kernel)
theorem intervalAccepted0212 : candidateIntervalCheck candidate0212 (989/10000) (991/10000) piece0212=true := by decide +kernel
noncomputable def cell0212 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0212 accepted0212 (989/10000) (991/10000) piece0212
    intervalAccepted0212 (fun t => piece_le_psi ⟨172,by decide +kernel⟩ t)
def piece0213 : AffinePiece := pieces[173]'(by decide +kernel)
theorem intervalAccepted0213 : candidateIntervalCheck candidate0213 (991/10000) (993/10000) piece0213=true := by decide +kernel
noncomputable def cell0213 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0213 accepted0213 (991/10000) (993/10000) piece0213
    intervalAccepted0213 (fun t => piece_le_psi ⟨173,by decide +kernel⟩ t)
def piece0214 : AffinePiece := pieces[174]'(by decide +kernel)
theorem intervalAccepted0214 : candidateIntervalCheck candidate0214 (993/10000) (199/2000) piece0214=true := by decide +kernel
noncomputable def cell0214 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0214 accepted0214 (993/10000) (199/2000) piece0214
    intervalAccepted0214 (fun t => piece_le_psi ⟨174,by decide +kernel⟩ t)
def piece0215 : AffinePiece := pieces[175]'(by decide +kernel)
theorem intervalAccepted0215 : candidateIntervalCheck candidate0215 (199/2000) (997/10000) piece0215=true := by decide +kernel
noncomputable def cell0215 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0215 accepted0215 (199/2000) (997/10000) piece0215
    intervalAccepted0215 (fun t => piece_le_psi ⟨175,by decide +kernel⟩ t)
def piece0216 : AffinePiece := pieces[176]'(by decide +kernel)
theorem intervalAccepted0216 : candidateIntervalCheck candidate0216 (997/10000) (999/10000) piece0216=true := by decide +kernel
noncomputable def cell0216 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0216 accepted0216 (997/10000) (999/10000) piece0216
    intervalAccepted0216 (fun t => piece_le_psi ⟨176,by decide +kernel⟩ t)
def piece0217 : AffinePiece := pieces[177]'(by decide +kernel)
theorem intervalAccepted0217 : candidateIntervalCheck candidate0217 (999/10000) (1001/10000) piece0217=true := by decide +kernel
noncomputable def cell0217 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0217 accepted0217 (999/10000) (1001/10000) piece0217
    intervalAccepted0217 (fun t => piece_le_psi ⟨177,by decide +kernel⟩ t)
def piece0218 : AffinePiece := pieces[178]'(by decide +kernel)
theorem intervalAccepted0218 : candidateIntervalCheck candidate0218 (1001/10000) (1003/10000) piece0218=true := by decide +kernel
noncomputable def cell0218 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0218 accepted0218 (1001/10000) (1003/10000) piece0218
    intervalAccepted0218 (fun t => piece_le_psi ⟨178,by decide +kernel⟩ t)
def piece0219 : AffinePiece := pieces[179]'(by decide +kernel)
theorem intervalAccepted0219 : candidateIntervalCheck candidate0219 (1003/10000) (201/2000) piece0219=true := by decide +kernel
noncomputable def cell0219 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0219 accepted0219 (1003/10000) (201/2000) piece0219
    intervalAccepted0219 (fun t => piece_le_psi ⟨179,by decide +kernel⟩ t)
def piece0220 : AffinePiece := pieces[180]'(by decide +kernel)
theorem intervalAccepted0220 : candidateIntervalCheck candidate0220 (201/2000) (1007/10000) piece0220=true := by decide +kernel
noncomputable def cell0220 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0220 accepted0220 (201/2000) (1007/10000) piece0220
    intervalAccepted0220 (fun t => piece_le_psi ⟨180,by decide +kernel⟩ t)
def piece0221 : AffinePiece := pieces[181]'(by decide +kernel)
theorem intervalAccepted0221 : candidateIntervalCheck candidate0221 (1007/10000) (1009/10000) piece0221=true := by decide +kernel
noncomputable def cell0221 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0221 accepted0221 (1007/10000) (1009/10000) piece0221
    intervalAccepted0221 (fun t => piece_le_psi ⟨181,by decide +kernel⟩ t)
def piece0222 : AffinePiece := pieces[182]'(by decide +kernel)
theorem intervalAccepted0222 : candidateIntervalCheck candidate0222 (1009/10000) (1011/10000) piece0222=true := by decide +kernel
noncomputable def cell0222 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0222 accepted0222 (1009/10000) (1011/10000) piece0222
    intervalAccepted0222 (fun t => piece_le_psi ⟨182,by decide +kernel⟩ t)
def piece0223 : AffinePiece := pieces[183]'(by decide +kernel)
theorem intervalAccepted0223 : candidateIntervalCheck candidate0223 (1011/10000) (1013/10000) piece0223=true := by decide +kernel
noncomputable def cell0223 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0223 accepted0223 (1011/10000) (1013/10000) piece0223
    intervalAccepted0223 (fun t => piece_le_psi ⟨183,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0208, cell0209, cell0210, cell0211, cell0212, cell0213, cell0214, cell0215, cell0216, cell0217, cell0218, cell0219, cell0220, cell0221, cell0222, cell0223]
theorem chainAccepted : spinCellChainCheck (981/10000) (1013/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (981/10000) (1013/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0013
