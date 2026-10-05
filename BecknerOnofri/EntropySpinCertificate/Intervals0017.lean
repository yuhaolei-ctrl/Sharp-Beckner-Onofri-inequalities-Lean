import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0017
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0017
open CandidateBatch0017 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0272 : AffinePiece := pieces[232]'(by decide +kernel)
theorem intervalAccepted0272 : candidateIntervalCheck candidate0272 (1109/10000) (1111/10000) piece0272=true := by decide +kernel
noncomputable def cell0272 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0272 accepted0272 (1109/10000) (1111/10000) piece0272
    intervalAccepted0272 (fun t => piece_le_psi ⟨232,by decide +kernel⟩ t)
def piece0273 : AffinePiece := pieces[233]'(by decide +kernel)
theorem intervalAccepted0273 : candidateIntervalCheck candidate0273 (1111/10000) (1113/10000) piece0273=true := by decide +kernel
noncomputable def cell0273 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0273 accepted0273 (1111/10000) (1113/10000) piece0273
    intervalAccepted0273 (fun t => piece_le_psi ⟨233,by decide +kernel⟩ t)
def piece0274 : AffinePiece := pieces[234]'(by decide +kernel)
theorem intervalAccepted0274 : candidateIntervalCheck candidate0274 (1113/10000) (223/2000) piece0274=true := by decide +kernel
noncomputable def cell0274 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0274 accepted0274 (1113/10000) (223/2000) piece0274
    intervalAccepted0274 (fun t => piece_le_psi ⟨234,by decide +kernel⟩ t)
def piece0275 : AffinePiece := pieces[235]'(by decide +kernel)
theorem intervalAccepted0275 : candidateIntervalCheck candidate0275 (223/2000) (1117/10000) piece0275=true := by decide +kernel
noncomputable def cell0275 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0275 accepted0275 (223/2000) (1117/10000) piece0275
    intervalAccepted0275 (fun t => piece_le_psi ⟨235,by decide +kernel⟩ t)
def piece0276 : AffinePiece := pieces[236]'(by decide +kernel)
theorem intervalAccepted0276 : candidateIntervalCheck candidate0276 (1117/10000) (1119/10000) piece0276=true := by decide +kernel
noncomputable def cell0276 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0276 accepted0276 (1117/10000) (1119/10000) piece0276
    intervalAccepted0276 (fun t => piece_le_psi ⟨236,by decide +kernel⟩ t)
def piece0277 : AffinePiece := pieces[237]'(by decide +kernel)
theorem intervalAccepted0277 : candidateIntervalCheck candidate0277 (1119/10000) (1121/10000) piece0277=true := by decide +kernel
noncomputable def cell0277 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0277 accepted0277 (1119/10000) (1121/10000) piece0277
    intervalAccepted0277 (fun t => piece_le_psi ⟨237,by decide +kernel⟩ t)
def piece0278 : AffinePiece := pieces[238]'(by decide +kernel)
theorem intervalAccepted0278 : candidateIntervalCheck candidate0278 (1121/10000) (1123/10000) piece0278=true := by decide +kernel
noncomputable def cell0278 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0278 accepted0278 (1121/10000) (1123/10000) piece0278
    intervalAccepted0278 (fun t => piece_le_psi ⟨238,by decide +kernel⟩ t)
def piece0279 : AffinePiece := pieces[239]'(by decide +kernel)
theorem intervalAccepted0279 : candidateIntervalCheck candidate0279 (1123/10000) (9/80) piece0279=true := by decide +kernel
noncomputable def cell0279 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0279 accepted0279 (1123/10000) (9/80) piece0279
    intervalAccepted0279 (fun t => piece_le_psi ⟨239,by decide +kernel⟩ t)
def piece0280 : AffinePiece := pieces[240]'(by decide +kernel)
theorem intervalAccepted0280 : candidateIntervalCheck candidate0280 (9/80) (1127/10000) piece0280=true := by decide +kernel
noncomputable def cell0280 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0280 accepted0280 (9/80) (1127/10000) piece0280
    intervalAccepted0280 (fun t => piece_le_psi ⟨240,by decide +kernel⟩ t)
def piece0281 : AffinePiece := pieces[241]'(by decide +kernel)
theorem intervalAccepted0281 : candidateIntervalCheck candidate0281 (1127/10000) (1129/10000) piece0281=true := by decide +kernel
noncomputable def cell0281 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0281 accepted0281 (1127/10000) (1129/10000) piece0281
    intervalAccepted0281 (fun t => piece_le_psi ⟨241,by decide +kernel⟩ t)
def piece0282 : AffinePiece := pieces[242]'(by decide +kernel)
theorem intervalAccepted0282 : candidateIntervalCheck candidate0282 (1129/10000) (1131/10000) piece0282=true := by decide +kernel
noncomputable def cell0282 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0282 accepted0282 (1129/10000) (1131/10000) piece0282
    intervalAccepted0282 (fun t => piece_le_psi ⟨242,by decide +kernel⟩ t)
def piece0283 : AffinePiece := pieces[243]'(by decide +kernel)
theorem intervalAccepted0283 : candidateIntervalCheck candidate0283 (1131/10000) (1133/10000) piece0283=true := by decide +kernel
noncomputable def cell0283 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0283 accepted0283 (1131/10000) (1133/10000) piece0283
    intervalAccepted0283 (fun t => piece_le_psi ⟨243,by decide +kernel⟩ t)
def piece0284 : AffinePiece := pieces[244]'(by decide +kernel)
theorem intervalAccepted0284 : candidateIntervalCheck candidate0284 (1133/10000) (227/2000) piece0284=true := by decide +kernel
noncomputable def cell0284 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0284 accepted0284 (1133/10000) (227/2000) piece0284
    intervalAccepted0284 (fun t => piece_le_psi ⟨244,by decide +kernel⟩ t)
def piece0285 : AffinePiece := pieces[245]'(by decide +kernel)
theorem intervalAccepted0285 : candidateIntervalCheck candidate0285 (227/2000) (1137/10000) piece0285=true := by decide +kernel
noncomputable def cell0285 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0285 accepted0285 (227/2000) (1137/10000) piece0285
    intervalAccepted0285 (fun t => piece_le_psi ⟨245,by decide +kernel⟩ t)
def piece0286 : AffinePiece := pieces[246]'(by decide +kernel)
theorem intervalAccepted0286 : candidateIntervalCheck candidate0286 (1137/10000) (1139/10000) piece0286=true := by decide +kernel
noncomputable def cell0286 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0286 accepted0286 (1137/10000) (1139/10000) piece0286
    intervalAccepted0286 (fun t => piece_le_psi ⟨246,by decide +kernel⟩ t)
def piece0287 : AffinePiece := pieces[247]'(by decide +kernel)
theorem intervalAccepted0287 : candidateIntervalCheck candidate0287 (1139/10000) (1141/10000) piece0287=true := by decide +kernel
noncomputable def cell0287 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0287 accepted0287 (1139/10000) (1141/10000) piece0287
    intervalAccepted0287 (fun t => piece_le_psi ⟨247,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0272, cell0273, cell0274, cell0275, cell0276, cell0277, cell0278, cell0279, cell0280, cell0281, cell0282, cell0283, cell0284, cell0285, cell0286, cell0287]
theorem chainAccepted : spinCellChainCheck (1109/10000) (1141/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1109/10000) (1141/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0017
