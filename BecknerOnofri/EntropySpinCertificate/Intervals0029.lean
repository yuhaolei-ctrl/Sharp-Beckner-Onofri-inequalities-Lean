import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0029
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0029
open CandidateBatch0029 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0464 : AffinePiece := pieces[424]'(by decide +kernel)
theorem intervalAccepted0464 : candidateIntervalCheck candidate0464 (1493/10000) (299/2000) piece0464=true := by decide +kernel
noncomputable def cell0464 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0464 accepted0464 (1493/10000) (299/2000) piece0464
    intervalAccepted0464 (fun t => piece_le_psi ⟨424,by decide +kernel⟩ t)
def piece0465 : AffinePiece := pieces[425]'(by decide +kernel)
theorem intervalAccepted0465 : candidateIntervalCheck candidate0465 (299/2000) (1497/10000) piece0465=true := by decide +kernel
noncomputable def cell0465 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0465 accepted0465 (299/2000) (1497/10000) piece0465
    intervalAccepted0465 (fun t => piece_le_psi ⟨425,by decide +kernel⟩ t)
def piece0466 : AffinePiece := pieces[426]'(by decide +kernel)
theorem intervalAccepted0466 : candidateIntervalCheck candidate0466 (1497/10000) (1499/10000) piece0466=true := by decide +kernel
noncomputable def cell0466 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0466 accepted0466 (1497/10000) (1499/10000) piece0466
    intervalAccepted0466 (fun t => piece_le_psi ⟨426,by decide +kernel⟩ t)
def piece0467 : AffinePiece := pieces[427]'(by decide +kernel)
theorem intervalAccepted0467 : candidateIntervalCheck candidate0467 (1499/10000) (1501/10000) piece0467=true := by decide +kernel
noncomputable def cell0467 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0467 accepted0467 (1499/10000) (1501/10000) piece0467
    intervalAccepted0467 (fun t => piece_le_psi ⟨427,by decide +kernel⟩ t)
def piece0468 : AffinePiece := pieces[428]'(by decide +kernel)
theorem intervalAccepted0468 : candidateIntervalCheck candidate0468 (1501/10000) (1503/10000) piece0468=true := by decide +kernel
noncomputable def cell0468 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0468 accepted0468 (1501/10000) (1503/10000) piece0468
    intervalAccepted0468 (fun t => piece_le_psi ⟨428,by decide +kernel⟩ t)
def piece0469 : AffinePiece := pieces[429]'(by decide +kernel)
theorem intervalAccepted0469 : candidateIntervalCheck candidate0469 (1503/10000) (301/2000) piece0469=true := by decide +kernel
noncomputable def cell0469 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0469 accepted0469 (1503/10000) (301/2000) piece0469
    intervalAccepted0469 (fun t => piece_le_psi ⟨429,by decide +kernel⟩ t)
def piece0470 : AffinePiece := pieces[430]'(by decide +kernel)
theorem intervalAccepted0470 : candidateIntervalCheck candidate0470 (301/2000) (1507/10000) piece0470=true := by decide +kernel
noncomputable def cell0470 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0470 accepted0470 (301/2000) (1507/10000) piece0470
    intervalAccepted0470 (fun t => piece_le_psi ⟨430,by decide +kernel⟩ t)
def piece0471 : AffinePiece := pieces[431]'(by decide +kernel)
theorem intervalAccepted0471 : candidateIntervalCheck candidate0471 (1507/10000) (1509/10000) piece0471=true := by decide +kernel
noncomputable def cell0471 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0471 accepted0471 (1507/10000) (1509/10000) piece0471
    intervalAccepted0471 (fun t => piece_le_psi ⟨431,by decide +kernel⟩ t)
def piece0472 : AffinePiece := pieces[432]'(by decide +kernel)
theorem intervalAccepted0472 : candidateIntervalCheck candidate0472 (1509/10000) (1511/10000) piece0472=true := by decide +kernel
noncomputable def cell0472 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0472 accepted0472 (1509/10000) (1511/10000) piece0472
    intervalAccepted0472 (fun t => piece_le_psi ⟨432,by decide +kernel⟩ t)
def piece0473 : AffinePiece := pieces[433]'(by decide +kernel)
theorem intervalAccepted0473 : candidateIntervalCheck candidate0473 (1511/10000) (1513/10000) piece0473=true := by decide +kernel
noncomputable def cell0473 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0473 accepted0473 (1511/10000) (1513/10000) piece0473
    intervalAccepted0473 (fun t => piece_le_psi ⟨433,by decide +kernel⟩ t)
def piece0474 : AffinePiece := pieces[434]'(by decide +kernel)
theorem intervalAccepted0474 : candidateIntervalCheck candidate0474 (1513/10000) (303/2000) piece0474=true := by decide +kernel
noncomputable def cell0474 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0474 accepted0474 (1513/10000) (303/2000) piece0474
    intervalAccepted0474 (fun t => piece_le_psi ⟨434,by decide +kernel⟩ t)
def piece0475 : AffinePiece := pieces[435]'(by decide +kernel)
theorem intervalAccepted0475 : candidateIntervalCheck candidate0475 (303/2000) (1517/10000) piece0475=true := by decide +kernel
noncomputable def cell0475 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0475 accepted0475 (303/2000) (1517/10000) piece0475
    intervalAccepted0475 (fun t => piece_le_psi ⟨435,by decide +kernel⟩ t)
def piece0476 : AffinePiece := pieces[436]'(by decide +kernel)
theorem intervalAccepted0476 : candidateIntervalCheck candidate0476 (1517/10000) (1519/10000) piece0476=true := by decide +kernel
noncomputable def cell0476 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0476 accepted0476 (1517/10000) (1519/10000) piece0476
    intervalAccepted0476 (fun t => piece_le_psi ⟨436,by decide +kernel⟩ t)
def piece0477 : AffinePiece := pieces[437]'(by decide +kernel)
theorem intervalAccepted0477 : candidateIntervalCheck candidate0477 (1519/10000) (1521/10000) piece0477=true := by decide +kernel
noncomputable def cell0477 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0477 accepted0477 (1519/10000) (1521/10000) piece0477
    intervalAccepted0477 (fun t => piece_le_psi ⟨437,by decide +kernel⟩ t)
def piece0478 : AffinePiece := pieces[438]'(by decide +kernel)
theorem intervalAccepted0478 : candidateIntervalCheck candidate0478 (1521/10000) (1523/10000) piece0478=true := by decide +kernel
noncomputable def cell0478 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0478 accepted0478 (1521/10000) (1523/10000) piece0478
    intervalAccepted0478 (fun t => piece_le_psi ⟨438,by decide +kernel⟩ t)
def piece0479 : AffinePiece := pieces[439]'(by decide +kernel)
theorem intervalAccepted0479 : candidateIntervalCheck candidate0479 (1523/10000) (61/400) piece0479=true := by decide +kernel
noncomputable def cell0479 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0479 accepted0479 (1523/10000) (61/400) piece0479
    intervalAccepted0479 (fun t => piece_le_psi ⟨439,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0464, cell0465, cell0466, cell0467, cell0468, cell0469, cell0470, cell0471, cell0472, cell0473, cell0474, cell0475, cell0476, cell0477, cell0478, cell0479]
theorem chainAccepted : spinCellChainCheck (1493/10000) (61/400) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1493/10000) (61/400) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0029
