module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0086

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0086
open CandidateBatch0086 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1376 : AffinePiece := pieces[1247]'(by decide +kernel)
theorem intervalAccepted1376 : candidateIntervalCheck candidate1376 (829/1000) (1659/2000) piece1376=true := by decide +kernel
noncomputable def cell1376 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1376 accepted1376 (829/1000) (1659/2000) piece1376
    intervalAccepted1376 (fun t => piece_le_psi ⟨1247,by decide +kernel⟩ t)
def piece1377 : AffinePiece := pieces[1248]'(by decide +kernel)
theorem intervalAccepted1377 : candidateIntervalCheck candidate1377 (1659/2000) (83/100) piece1377=true := by decide +kernel
noncomputable def cell1377 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1377 accepted1377 (1659/2000) (83/100) piece1377
    intervalAccepted1377 (fun t => piece_le_psi ⟨1248,by decide +kernel⟩ t)
def piece1378 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1378 : candidateIntervalCheck candidate1378 (83/100) (8301/10000) piece1378=true := by decide +kernel
noncomputable def cell1378 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1378 accepted1378 (83/100) (8301/10000) piece1378
    intervalAccepted1378 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1379 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1379 : candidateIntervalCheck candidate1379 (8301/10000) (4151/5000) piece1379=true := by decide +kernel
noncomputable def cell1379 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1379 accepted1379 (8301/10000) (4151/5000) piece1379
    intervalAccepted1379 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1380 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1380 : candidateIntervalCheck candidate1380 (4151/5000) (8303/10000) piece1380=true := by decide +kernel
noncomputable def cell1380 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1380 accepted1380 (4151/5000) (8303/10000) piece1380
    intervalAccepted1380 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1381 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1381 : candidateIntervalCheck candidate1381 (8303/10000) (519/625) piece1381=true := by decide +kernel
noncomputable def cell1381 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1381 accepted1381 (8303/10000) (519/625) piece1381
    intervalAccepted1381 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1382 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1382 : candidateIntervalCheck candidate1382 (519/625) (1661/2000) piece1382=true := by decide +kernel
noncomputable def cell1382 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1382 accepted1382 (519/625) (1661/2000) piece1382
    intervalAccepted1382 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1383 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1383 : candidateIntervalCheck candidate1383 (1661/2000) (4153/5000) piece1383=true := by decide +kernel
noncomputable def cell1383 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1383 accepted1383 (1661/2000) (4153/5000) piece1383
    intervalAccepted1383 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1384 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1384 : candidateIntervalCheck candidate1384 (4153/5000) (8307/10000) piece1384=true := by decide +kernel
noncomputable def cell1384 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1384 accepted1384 (4153/5000) (8307/10000) piece1384
    intervalAccepted1384 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1385 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1385 : candidateIntervalCheck candidate1385 (8307/10000) (2077/2500) piece1385=true := by decide +kernel
noncomputable def cell1385 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1385 accepted1385 (8307/10000) (2077/2500) piece1385
    intervalAccepted1385 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1386 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1386 : candidateIntervalCheck candidate1386 (2077/2500) (8309/10000) piece1386=true := by decide +kernel
noncomputable def cell1386 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1386 accepted1386 (2077/2500) (8309/10000) piece1386
    intervalAccepted1386 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1387 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1387 : candidateIntervalCheck candidate1387 (8309/10000) (831/1000) piece1387=true := by decide +kernel
noncomputable def cell1387 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1387 accepted1387 (8309/10000) (831/1000) piece1387
    intervalAccepted1387 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1388 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1388 : candidateIntervalCheck candidate1388 (831/1000) (8311/10000) piece1388=true := by decide +kernel
noncomputable def cell1388 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1388 accepted1388 (831/1000) (8311/10000) piece1388
    intervalAccepted1388 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1389 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1389 : candidateIntervalCheck candidate1389 (8311/10000) (1039/1250) piece1389=true := by decide +kernel
noncomputable def cell1389 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1389 accepted1389 (8311/10000) (1039/1250) piece1389
    intervalAccepted1389 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1390 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1390 : candidateIntervalCheck candidate1390 (1039/1250) (8313/10000) piece1390=true := by decide +kernel
noncomputable def cell1390 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1390 accepted1390 (1039/1250) (8313/10000) piece1390
    intervalAccepted1390 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
def piece1391 : AffinePiece := pieces[1249]'(by decide +kernel)
theorem intervalAccepted1391 : candidateIntervalCheck candidate1391 (8313/10000) (4157/5000) piece1391=true := by decide +kernel
noncomputable def cell1391 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1391 accepted1391 (8313/10000) (4157/5000) piece1391
    intervalAccepted1391 (fun t => piece_le_psi ⟨1249,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1376, cell1377, cell1378, cell1379, cell1380, cell1381, cell1382, cell1383, cell1384, cell1385, cell1386, cell1387, cell1388, cell1389, cell1390, cell1391]
theorem chainAccepted : spinCellChainCheck (829/1000) (4157/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (829/1000) (4157/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0086
