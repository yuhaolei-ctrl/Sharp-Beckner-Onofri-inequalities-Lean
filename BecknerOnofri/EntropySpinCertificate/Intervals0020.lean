module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0020

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0020
open CandidateBatch0020 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0320 : AffinePiece := pieces[280]'(by decide +kernel)
theorem intervalAccepted0320 : candidateIntervalCheck candidate0320 (241/2000) (1207/10000) piece0320=true := by decide +kernel
noncomputable def cell0320 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0320 accepted0320 (241/2000) (1207/10000) piece0320
    intervalAccepted0320 (fun t => piece_le_psi ⟨280,by decide +kernel⟩ t)
def piece0321 : AffinePiece := pieces[281]'(by decide +kernel)
theorem intervalAccepted0321 : candidateIntervalCheck candidate0321 (1207/10000) (1209/10000) piece0321=true := by decide +kernel
noncomputable def cell0321 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0321 accepted0321 (1207/10000) (1209/10000) piece0321
    intervalAccepted0321 (fun t => piece_le_psi ⟨281,by decide +kernel⟩ t)
def piece0322 : AffinePiece := pieces[282]'(by decide +kernel)
theorem intervalAccepted0322 : candidateIntervalCheck candidate0322 (1209/10000) (1211/10000) piece0322=true := by decide +kernel
noncomputable def cell0322 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0322 accepted0322 (1209/10000) (1211/10000) piece0322
    intervalAccepted0322 (fun t => piece_le_psi ⟨282,by decide +kernel⟩ t)
def piece0323 : AffinePiece := pieces[283]'(by decide +kernel)
theorem intervalAccepted0323 : candidateIntervalCheck candidate0323 (1211/10000) (1213/10000) piece0323=true := by decide +kernel
noncomputable def cell0323 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0323 accepted0323 (1211/10000) (1213/10000) piece0323
    intervalAccepted0323 (fun t => piece_le_psi ⟨283,by decide +kernel⟩ t)
def piece0324 : AffinePiece := pieces[284]'(by decide +kernel)
theorem intervalAccepted0324 : candidateIntervalCheck candidate0324 (1213/10000) (243/2000) piece0324=true := by decide +kernel
noncomputable def cell0324 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0324 accepted0324 (1213/10000) (243/2000) piece0324
    intervalAccepted0324 (fun t => piece_le_psi ⟨284,by decide +kernel⟩ t)
def piece0325 : AffinePiece := pieces[285]'(by decide +kernel)
theorem intervalAccepted0325 : candidateIntervalCheck candidate0325 (243/2000) (1217/10000) piece0325=true := by decide +kernel
noncomputable def cell0325 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0325 accepted0325 (243/2000) (1217/10000) piece0325
    intervalAccepted0325 (fun t => piece_le_psi ⟨285,by decide +kernel⟩ t)
def piece0326 : AffinePiece := pieces[286]'(by decide +kernel)
theorem intervalAccepted0326 : candidateIntervalCheck candidate0326 (1217/10000) (1219/10000) piece0326=true := by decide +kernel
noncomputable def cell0326 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0326 accepted0326 (1217/10000) (1219/10000) piece0326
    intervalAccepted0326 (fun t => piece_le_psi ⟨286,by decide +kernel⟩ t)
def piece0327 : AffinePiece := pieces[287]'(by decide +kernel)
theorem intervalAccepted0327 : candidateIntervalCheck candidate0327 (1219/10000) (1221/10000) piece0327=true := by decide +kernel
noncomputable def cell0327 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0327 accepted0327 (1219/10000) (1221/10000) piece0327
    intervalAccepted0327 (fun t => piece_le_psi ⟨287,by decide +kernel⟩ t)
def piece0328 : AffinePiece := pieces[288]'(by decide +kernel)
theorem intervalAccepted0328 : candidateIntervalCheck candidate0328 (1221/10000) (1223/10000) piece0328=true := by decide +kernel
noncomputable def cell0328 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0328 accepted0328 (1221/10000) (1223/10000) piece0328
    intervalAccepted0328 (fun t => piece_le_psi ⟨288,by decide +kernel⟩ t)
def piece0329 : AffinePiece := pieces[289]'(by decide +kernel)
theorem intervalAccepted0329 : candidateIntervalCheck candidate0329 (1223/10000) (49/400) piece0329=true := by decide +kernel
noncomputable def cell0329 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0329 accepted0329 (1223/10000) (49/400) piece0329
    intervalAccepted0329 (fun t => piece_le_psi ⟨289,by decide +kernel⟩ t)
def piece0330 : AffinePiece := pieces[290]'(by decide +kernel)
theorem intervalAccepted0330 : candidateIntervalCheck candidate0330 (49/400) (1227/10000) piece0330=true := by decide +kernel
noncomputable def cell0330 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0330 accepted0330 (49/400) (1227/10000) piece0330
    intervalAccepted0330 (fun t => piece_le_psi ⟨290,by decide +kernel⟩ t)
def piece0331 : AffinePiece := pieces[291]'(by decide +kernel)
theorem intervalAccepted0331 : candidateIntervalCheck candidate0331 (1227/10000) (1229/10000) piece0331=true := by decide +kernel
noncomputable def cell0331 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0331 accepted0331 (1227/10000) (1229/10000) piece0331
    intervalAccepted0331 (fun t => piece_le_psi ⟨291,by decide +kernel⟩ t)
def piece0332 : AffinePiece := pieces[292]'(by decide +kernel)
theorem intervalAccepted0332 : candidateIntervalCheck candidate0332 (1229/10000) (1231/10000) piece0332=true := by decide +kernel
noncomputable def cell0332 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0332 accepted0332 (1229/10000) (1231/10000) piece0332
    intervalAccepted0332 (fun t => piece_le_psi ⟨292,by decide +kernel⟩ t)
def piece0333 : AffinePiece := pieces[293]'(by decide +kernel)
theorem intervalAccepted0333 : candidateIntervalCheck candidate0333 (1231/10000) (1233/10000) piece0333=true := by decide +kernel
noncomputable def cell0333 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0333 accepted0333 (1231/10000) (1233/10000) piece0333
    intervalAccepted0333 (fun t => piece_le_psi ⟨293,by decide +kernel⟩ t)
def piece0334 : AffinePiece := pieces[294]'(by decide +kernel)
theorem intervalAccepted0334 : candidateIntervalCheck candidate0334 (1233/10000) (247/2000) piece0334=true := by decide +kernel
noncomputable def cell0334 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0334 accepted0334 (1233/10000) (247/2000) piece0334
    intervalAccepted0334 (fun t => piece_le_psi ⟨294,by decide +kernel⟩ t)
def piece0335 : AffinePiece := pieces[295]'(by decide +kernel)
theorem intervalAccepted0335 : candidateIntervalCheck candidate0335 (247/2000) (1237/10000) piece0335=true := by decide +kernel
noncomputable def cell0335 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0335 accepted0335 (247/2000) (1237/10000) piece0335
    intervalAccepted0335 (fun t => piece_le_psi ⟨295,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0320, cell0321, cell0322, cell0323, cell0324, cell0325, cell0326, cell0327, cell0328, cell0329, cell0330, cell0331, cell0332, cell0333, cell0334, cell0335]
theorem chainAccepted : spinCellChainCheck (241/2000) (1237/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (241/2000) (1237/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0020
