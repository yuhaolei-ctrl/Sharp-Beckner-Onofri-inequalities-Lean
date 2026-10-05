import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0083
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0083
open CandidateBatch0083 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1328 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1328 : candidateIntervalCheck candidate1328 (161/200) (1611/2000) piece1328=true := by decide +kernel
noncomputable def cell1328 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1328 accepted1328 (161/200) (1611/2000) piece1328
    intervalAccepted1328 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1329 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1329 : candidateIntervalCheck candidate1329 (1611/2000) (403/500) piece1329=true := by decide +kernel
noncomputable def cell1329 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1329 accepted1329 (1611/2000) (403/500) piece1329
    intervalAccepted1329 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1330 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1330 : candidateIntervalCheck candidate1330 (403/500) (1613/2000) piece1330=true := by decide +kernel
noncomputable def cell1330 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1330 accepted1330 (403/500) (1613/2000) piece1330
    intervalAccepted1330 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1331 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1331 : candidateIntervalCheck candidate1331 (1613/2000) (807/1000) piece1331=true := by decide +kernel
noncomputable def cell1331 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1331 accepted1331 (1613/2000) (807/1000) piece1331
    intervalAccepted1331 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1332 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1332 : candidateIntervalCheck candidate1332 (807/1000) (323/400) piece1332=true := by decide +kernel
noncomputable def cell1332 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1332 accepted1332 (807/1000) (323/400) piece1332
    intervalAccepted1332 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1333 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1333 : candidateIntervalCheck candidate1333 (323/400) (101/125) piece1333=true := by decide +kernel
noncomputable def cell1333 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1333 accepted1333 (323/400) (101/125) piece1333
    intervalAccepted1333 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1334 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1334 : candidateIntervalCheck candidate1334 (101/125) (1617/2000) piece1334=true := by decide +kernel
noncomputable def cell1334 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1334 accepted1334 (101/125) (1617/2000) piece1334
    intervalAccepted1334 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1335 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1335 : candidateIntervalCheck candidate1335 (1617/2000) (809/1000) piece1335=true := by decide +kernel
noncomputable def cell1335 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1335 accepted1335 (1617/2000) (809/1000) piece1335
    intervalAccepted1335 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1336 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1336 : candidateIntervalCheck candidate1336 (809/1000) (1619/2000) piece1336=true := by decide +kernel
noncomputable def cell1336 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1336 accepted1336 (809/1000) (1619/2000) piece1336
    intervalAccepted1336 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1337 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1337 : candidateIntervalCheck candidate1337 (1619/2000) (81/100) piece1337=true := by decide +kernel
noncomputable def cell1337 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1337 accepted1337 (1619/2000) (81/100) piece1337
    intervalAccepted1337 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1338 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1338 : candidateIntervalCheck candidate1338 (81/100) (1621/2000) piece1338=true := by decide +kernel
noncomputable def cell1338 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1338 accepted1338 (81/100) (1621/2000) piece1338
    intervalAccepted1338 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1339 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1339 : candidateIntervalCheck candidate1339 (1621/2000) (811/1000) piece1339=true := by decide +kernel
noncomputable def cell1339 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1339 accepted1339 (1621/2000) (811/1000) piece1339
    intervalAccepted1339 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1340 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1340 : candidateIntervalCheck candidate1340 (811/1000) (1623/2000) piece1340=true := by decide +kernel
noncomputable def cell1340 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1340 accepted1340 (811/1000) (1623/2000) piece1340
    intervalAccepted1340 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1341 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1341 : candidateIntervalCheck candidate1341 (1623/2000) (203/250) piece1341=true := by decide +kernel
noncomputable def cell1341 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1341 accepted1341 (1623/2000) (203/250) piece1341
    intervalAccepted1341 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1342 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1342 : candidateIntervalCheck candidate1342 (203/250) (13/16) piece1342=true := by decide +kernel
noncomputable def cell1342 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1342 accepted1342 (203/250) (13/16) piece1342
    intervalAccepted1342 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
def piece1343 : AffinePiece := pieces[1216]'(by decide +kernel)
theorem intervalAccepted1343 : candidateIntervalCheck candidate1343 (13/16) (813/1000) piece1343=true := by decide +kernel
noncomputable def cell1343 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1343 accepted1343 (13/16) (813/1000) piece1343
    intervalAccepted1343 (fun t => piece_le_psi ⟨1216,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1328, cell1329, cell1330, cell1331, cell1332, cell1333, cell1334, cell1335, cell1336, cell1337, cell1338, cell1339, cell1340, cell1341, cell1342, cell1343]
theorem chainAccepted : spinCellChainCheck (161/200) (813/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (161/200) (813/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0083
