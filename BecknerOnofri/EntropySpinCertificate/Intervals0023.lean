module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0023

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0023
open CandidateBatch0023 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0368 : AffinePiece := pieces[328]'(by decide +kernel)
theorem intervalAccepted0368 : candidateIntervalCheck candidate0368 (1301/10000) (1303/10000) piece0368=true := by decide +kernel
noncomputable def cell0368 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0368 accepted0368 (1301/10000) (1303/10000) piece0368
    intervalAccepted0368 (fun t => piece_le_psi ⟨328,by decide +kernel⟩ t)
def piece0369 : AffinePiece := pieces[329]'(by decide +kernel)
theorem intervalAccepted0369 : candidateIntervalCheck candidate0369 (1303/10000) (261/2000) piece0369=true := by decide +kernel
noncomputable def cell0369 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0369 accepted0369 (1303/10000) (261/2000) piece0369
    intervalAccepted0369 (fun t => piece_le_psi ⟨329,by decide +kernel⟩ t)
def piece0370 : AffinePiece := pieces[330]'(by decide +kernel)
theorem intervalAccepted0370 : candidateIntervalCheck candidate0370 (261/2000) (1307/10000) piece0370=true := by decide +kernel
noncomputable def cell0370 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0370 accepted0370 (261/2000) (1307/10000) piece0370
    intervalAccepted0370 (fun t => piece_le_psi ⟨330,by decide +kernel⟩ t)
def piece0371 : AffinePiece := pieces[331]'(by decide +kernel)
theorem intervalAccepted0371 : candidateIntervalCheck candidate0371 (1307/10000) (1309/10000) piece0371=true := by decide +kernel
noncomputable def cell0371 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0371 accepted0371 (1307/10000) (1309/10000) piece0371
    intervalAccepted0371 (fun t => piece_le_psi ⟨331,by decide +kernel⟩ t)
def piece0372 : AffinePiece := pieces[332]'(by decide +kernel)
theorem intervalAccepted0372 : candidateIntervalCheck candidate0372 (1309/10000) (1311/10000) piece0372=true := by decide +kernel
noncomputable def cell0372 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0372 accepted0372 (1309/10000) (1311/10000) piece0372
    intervalAccepted0372 (fun t => piece_le_psi ⟨332,by decide +kernel⟩ t)
def piece0373 : AffinePiece := pieces[333]'(by decide +kernel)
theorem intervalAccepted0373 : candidateIntervalCheck candidate0373 (1311/10000) (1313/10000) piece0373=true := by decide +kernel
noncomputable def cell0373 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0373 accepted0373 (1311/10000) (1313/10000) piece0373
    intervalAccepted0373 (fun t => piece_le_psi ⟨333,by decide +kernel⟩ t)
def piece0374 : AffinePiece := pieces[334]'(by decide +kernel)
theorem intervalAccepted0374 : candidateIntervalCheck candidate0374 (1313/10000) (263/2000) piece0374=true := by decide +kernel
noncomputable def cell0374 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0374 accepted0374 (1313/10000) (263/2000) piece0374
    intervalAccepted0374 (fun t => piece_le_psi ⟨334,by decide +kernel⟩ t)
def piece0375 : AffinePiece := pieces[335]'(by decide +kernel)
theorem intervalAccepted0375 : candidateIntervalCheck candidate0375 (263/2000) (1317/10000) piece0375=true := by decide +kernel
noncomputable def cell0375 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0375 accepted0375 (263/2000) (1317/10000) piece0375
    intervalAccepted0375 (fun t => piece_le_psi ⟨335,by decide +kernel⟩ t)
def piece0376 : AffinePiece := pieces[336]'(by decide +kernel)
theorem intervalAccepted0376 : candidateIntervalCheck candidate0376 (1317/10000) (1319/10000) piece0376=true := by decide +kernel
noncomputable def cell0376 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0376 accepted0376 (1317/10000) (1319/10000) piece0376
    intervalAccepted0376 (fun t => piece_le_psi ⟨336,by decide +kernel⟩ t)
def piece0377 : AffinePiece := pieces[337]'(by decide +kernel)
theorem intervalAccepted0377 : candidateIntervalCheck candidate0377 (1319/10000) (1321/10000) piece0377=true := by decide +kernel
noncomputable def cell0377 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0377 accepted0377 (1319/10000) (1321/10000) piece0377
    intervalAccepted0377 (fun t => piece_le_psi ⟨337,by decide +kernel⟩ t)
def piece0378 : AffinePiece := pieces[338]'(by decide +kernel)
theorem intervalAccepted0378 : candidateIntervalCheck candidate0378 (1321/10000) (1323/10000) piece0378=true := by decide +kernel
noncomputable def cell0378 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0378 accepted0378 (1321/10000) (1323/10000) piece0378
    intervalAccepted0378 (fun t => piece_le_psi ⟨338,by decide +kernel⟩ t)
def piece0379 : AffinePiece := pieces[339]'(by decide +kernel)
theorem intervalAccepted0379 : candidateIntervalCheck candidate0379 (1323/10000) (53/400) piece0379=true := by decide +kernel
noncomputable def cell0379 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0379 accepted0379 (1323/10000) (53/400) piece0379
    intervalAccepted0379 (fun t => piece_le_psi ⟨339,by decide +kernel⟩ t)
def piece0380 : AffinePiece := pieces[340]'(by decide +kernel)
theorem intervalAccepted0380 : candidateIntervalCheck candidate0380 (53/400) (1327/10000) piece0380=true := by decide +kernel
noncomputable def cell0380 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0380 accepted0380 (53/400) (1327/10000) piece0380
    intervalAccepted0380 (fun t => piece_le_psi ⟨340,by decide +kernel⟩ t)
def piece0381 : AffinePiece := pieces[341]'(by decide +kernel)
theorem intervalAccepted0381 : candidateIntervalCheck candidate0381 (1327/10000) (1329/10000) piece0381=true := by decide +kernel
noncomputable def cell0381 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0381 accepted0381 (1327/10000) (1329/10000) piece0381
    intervalAccepted0381 (fun t => piece_le_psi ⟨341,by decide +kernel⟩ t)
def piece0382 : AffinePiece := pieces[342]'(by decide +kernel)
theorem intervalAccepted0382 : candidateIntervalCheck candidate0382 (1329/10000) (1331/10000) piece0382=true := by decide +kernel
noncomputable def cell0382 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0382 accepted0382 (1329/10000) (1331/10000) piece0382
    intervalAccepted0382 (fun t => piece_le_psi ⟨342,by decide +kernel⟩ t)
def piece0383 : AffinePiece := pieces[343]'(by decide +kernel)
theorem intervalAccepted0383 : candidateIntervalCheck candidate0383 (1331/10000) (1333/10000) piece0383=true := by decide +kernel
noncomputable def cell0383 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0383 accepted0383 (1331/10000) (1333/10000) piece0383
    intervalAccepted0383 (fun t => piece_le_psi ⟨343,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0368, cell0369, cell0370, cell0371, cell0372, cell0373, cell0374, cell0375, cell0376, cell0377, cell0378, cell0379, cell0380, cell0381, cell0382, cell0383]
theorem chainAccepted : spinCellChainCheck (1301/10000) (1333/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1301/10000) (1333/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0023
