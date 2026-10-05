import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0085
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0085
open CandidateBatch0085 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1360 : AffinePiece := pieces[1231]'(by decide +kernel)
theorem intervalAccepted1360 : candidateIntervalCheck candidate1360 (821/1000) (1643/2000) piece1360=true := by decide +kernel
noncomputable def cell1360 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1360 accepted1360 (821/1000) (1643/2000) piece1360
    intervalAccepted1360 (fun t => piece_le_psi ⟨1231,by decide +kernel⟩ t)
def piece1361 : AffinePiece := pieces[1232]'(by decide +kernel)
theorem intervalAccepted1361 : candidateIntervalCheck candidate1361 (1643/2000) (411/500) piece1361=true := by decide +kernel
noncomputable def cell1361 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1361 accepted1361 (1643/2000) (411/500) piece1361
    intervalAccepted1361 (fun t => piece_le_psi ⟨1232,by decide +kernel⟩ t)
def piece1362 : AffinePiece := pieces[1233]'(by decide +kernel)
theorem intervalAccepted1362 : candidateIntervalCheck candidate1362 (411/500) (329/400) piece1362=true := by decide +kernel
noncomputable def cell1362 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1362 accepted1362 (411/500) (329/400) piece1362
    intervalAccepted1362 (fun t => piece_le_psi ⟨1233,by decide +kernel⟩ t)
def piece1363 : AffinePiece := pieces[1234]'(by decide +kernel)
theorem intervalAccepted1363 : candidateIntervalCheck candidate1363 (329/400) (823/1000) piece1363=true := by decide +kernel
noncomputable def cell1363 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1363 accepted1363 (329/400) (823/1000) piece1363
    intervalAccepted1363 (fun t => piece_le_psi ⟨1234,by decide +kernel⟩ t)
def piece1364 : AffinePiece := pieces[1235]'(by decide +kernel)
theorem intervalAccepted1364 : candidateIntervalCheck candidate1364 (823/1000) (1647/2000) piece1364=true := by decide +kernel
noncomputable def cell1364 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1364 accepted1364 (823/1000) (1647/2000) piece1364
    intervalAccepted1364 (fun t => piece_le_psi ⟨1235,by decide +kernel⟩ t)
def piece1365 : AffinePiece := pieces[1236]'(by decide +kernel)
theorem intervalAccepted1365 : candidateIntervalCheck candidate1365 (1647/2000) (103/125) piece1365=true := by decide +kernel
noncomputable def cell1365 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1365 accepted1365 (1647/2000) (103/125) piece1365
    intervalAccepted1365 (fun t => piece_le_psi ⟨1236,by decide +kernel⟩ t)
def piece1366 : AffinePiece := pieces[1237]'(by decide +kernel)
theorem intervalAccepted1366 : candidateIntervalCheck candidate1366 (103/125) (1649/2000) piece1366=true := by decide +kernel
noncomputable def cell1366 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1366 accepted1366 (103/125) (1649/2000) piece1366
    intervalAccepted1366 (fun t => piece_le_psi ⟨1237,by decide +kernel⟩ t)
def piece1367 : AffinePiece := pieces[1238]'(by decide +kernel)
theorem intervalAccepted1367 : candidateIntervalCheck candidate1367 (1649/2000) (33/40) piece1367=true := by decide +kernel
noncomputable def cell1367 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1367 accepted1367 (1649/2000) (33/40) piece1367
    intervalAccepted1367 (fun t => piece_le_psi ⟨1238,by decide +kernel⟩ t)
def piece1368 : AffinePiece := pieces[1239]'(by decide +kernel)
theorem intervalAccepted1368 : candidateIntervalCheck candidate1368 (33/40) (1651/2000) piece1368=true := by decide +kernel
noncomputable def cell1368 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1368 accepted1368 (33/40) (1651/2000) piece1368
    intervalAccepted1368 (fun t => piece_le_psi ⟨1239,by decide +kernel⟩ t)
def piece1369 : AffinePiece := pieces[1240]'(by decide +kernel)
theorem intervalAccepted1369 : candidateIntervalCheck candidate1369 (1651/2000) (413/500) piece1369=true := by decide +kernel
noncomputable def cell1369 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1369 accepted1369 (1651/2000) (413/500) piece1369
    intervalAccepted1369 (fun t => piece_le_psi ⟨1240,by decide +kernel⟩ t)
def piece1370 : AffinePiece := pieces[1241]'(by decide +kernel)
theorem intervalAccepted1370 : candidateIntervalCheck candidate1370 (413/500) (1653/2000) piece1370=true := by decide +kernel
noncomputable def cell1370 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1370 accepted1370 (413/500) (1653/2000) piece1370
    intervalAccepted1370 (fun t => piece_le_psi ⟨1241,by decide +kernel⟩ t)
def piece1371 : AffinePiece := pieces[1242]'(by decide +kernel)
theorem intervalAccepted1371 : candidateIntervalCheck candidate1371 (1653/2000) (827/1000) piece1371=true := by decide +kernel
noncomputable def cell1371 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1371 accepted1371 (1653/2000) (827/1000) piece1371
    intervalAccepted1371 (fun t => piece_le_psi ⟨1242,by decide +kernel⟩ t)
def piece1372 : AffinePiece := pieces[1243]'(by decide +kernel)
theorem intervalAccepted1372 : candidateIntervalCheck candidate1372 (827/1000) (331/400) piece1372=true := by decide +kernel
noncomputable def cell1372 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1372 accepted1372 (827/1000) (331/400) piece1372
    intervalAccepted1372 (fun t => piece_le_psi ⟨1243,by decide +kernel⟩ t)
def piece1373 : AffinePiece := pieces[1244]'(by decide +kernel)
theorem intervalAccepted1373 : candidateIntervalCheck candidate1373 (331/400) (207/250) piece1373=true := by decide +kernel
noncomputable def cell1373 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1373 accepted1373 (331/400) (207/250) piece1373
    intervalAccepted1373 (fun t => piece_le_psi ⟨1244,by decide +kernel⟩ t)
def piece1374 : AffinePiece := pieces[1245]'(by decide +kernel)
theorem intervalAccepted1374 : candidateIntervalCheck candidate1374 (207/250) (1657/2000) piece1374=true := by decide +kernel
noncomputable def cell1374 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1374 accepted1374 (207/250) (1657/2000) piece1374
    intervalAccepted1374 (fun t => piece_le_psi ⟨1245,by decide +kernel⟩ t)
def piece1375 : AffinePiece := pieces[1246]'(by decide +kernel)
theorem intervalAccepted1375 : candidateIntervalCheck candidate1375 (1657/2000) (829/1000) piece1375=true := by decide +kernel
noncomputable def cell1375 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1375 accepted1375 (1657/2000) (829/1000) piece1375
    intervalAccepted1375 (fun t => piece_le_psi ⟨1246,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1360, cell1361, cell1362, cell1363, cell1364, cell1365, cell1366, cell1367, cell1368, cell1369, cell1370, cell1371, cell1372, cell1373, cell1374, cell1375]
theorem chainAccepted : spinCellChainCheck (821/1000) (829/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (821/1000) (829/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0085
