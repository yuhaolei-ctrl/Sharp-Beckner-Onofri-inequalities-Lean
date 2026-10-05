import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0030
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0030
open CandidateBatch0030 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0480 : AffinePiece := pieces[440]'(by decide +kernel)
theorem intervalAccepted0480 : candidateIntervalCheck candidate0480 (61/400) (1527/10000) piece0480=true := by decide +kernel
noncomputable def cell0480 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0480 accepted0480 (61/400) (1527/10000) piece0480
    intervalAccepted0480 (fun t => piece_le_psi ⟨440,by decide +kernel⟩ t)
def piece0481 : AffinePiece := pieces[441]'(by decide +kernel)
theorem intervalAccepted0481 : candidateIntervalCheck candidate0481 (1527/10000) (1529/10000) piece0481=true := by decide +kernel
noncomputable def cell0481 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0481 accepted0481 (1527/10000) (1529/10000) piece0481
    intervalAccepted0481 (fun t => piece_le_psi ⟨441,by decide +kernel⟩ t)
def piece0482 : AffinePiece := pieces[442]'(by decide +kernel)
theorem intervalAccepted0482 : candidateIntervalCheck candidate0482 (1529/10000) (1531/10000) piece0482=true := by decide +kernel
noncomputable def cell0482 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0482 accepted0482 (1529/10000) (1531/10000) piece0482
    intervalAccepted0482 (fun t => piece_le_psi ⟨442,by decide +kernel⟩ t)
def piece0483 : AffinePiece := pieces[443]'(by decide +kernel)
theorem intervalAccepted0483 : candidateIntervalCheck candidate0483 (1531/10000) (1533/10000) piece0483=true := by decide +kernel
noncomputable def cell0483 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0483 accepted0483 (1531/10000) (1533/10000) piece0483
    intervalAccepted0483 (fun t => piece_le_psi ⟨443,by decide +kernel⟩ t)
def piece0484 : AffinePiece := pieces[444]'(by decide +kernel)
theorem intervalAccepted0484 : candidateIntervalCheck candidate0484 (1533/10000) (307/2000) piece0484=true := by decide +kernel
noncomputable def cell0484 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0484 accepted0484 (1533/10000) (307/2000) piece0484
    intervalAccepted0484 (fun t => piece_le_psi ⟨444,by decide +kernel⟩ t)
def piece0485 : AffinePiece := pieces[445]'(by decide +kernel)
theorem intervalAccepted0485 : candidateIntervalCheck candidate0485 (307/2000) (1537/10000) piece0485=true := by decide +kernel
noncomputable def cell0485 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0485 accepted0485 (307/2000) (1537/10000) piece0485
    intervalAccepted0485 (fun t => piece_le_psi ⟨445,by decide +kernel⟩ t)
def piece0486 : AffinePiece := pieces[446]'(by decide +kernel)
theorem intervalAccepted0486 : candidateIntervalCheck candidate0486 (1537/10000) (1539/10000) piece0486=true := by decide +kernel
noncomputable def cell0486 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0486 accepted0486 (1537/10000) (1539/10000) piece0486
    intervalAccepted0486 (fun t => piece_le_psi ⟨446,by decide +kernel⟩ t)
def piece0487 : AffinePiece := pieces[447]'(by decide +kernel)
theorem intervalAccepted0487 : candidateIntervalCheck candidate0487 (1539/10000) (1541/10000) piece0487=true := by decide +kernel
noncomputable def cell0487 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0487 accepted0487 (1539/10000) (1541/10000) piece0487
    intervalAccepted0487 (fun t => piece_le_psi ⟨447,by decide +kernel⟩ t)
def piece0488 : AffinePiece := pieces[448]'(by decide +kernel)
theorem intervalAccepted0488 : candidateIntervalCheck candidate0488 (1541/10000) (1543/10000) piece0488=true := by decide +kernel
noncomputable def cell0488 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0488 accepted0488 (1541/10000) (1543/10000) piece0488
    intervalAccepted0488 (fun t => piece_le_psi ⟨448,by decide +kernel⟩ t)
def piece0489 : AffinePiece := pieces[449]'(by decide +kernel)
theorem intervalAccepted0489 : candidateIntervalCheck candidate0489 (1543/10000) (309/2000) piece0489=true := by decide +kernel
noncomputable def cell0489 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0489 accepted0489 (1543/10000) (309/2000) piece0489
    intervalAccepted0489 (fun t => piece_le_psi ⟨449,by decide +kernel⟩ t)
def piece0490 : AffinePiece := pieces[450]'(by decide +kernel)
theorem intervalAccepted0490 : candidateIntervalCheck candidate0490 (309/2000) (1547/10000) piece0490=true := by decide +kernel
noncomputable def cell0490 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0490 accepted0490 (309/2000) (1547/10000) piece0490
    intervalAccepted0490 (fun t => piece_le_psi ⟨450,by decide +kernel⟩ t)
def piece0491 : AffinePiece := pieces[451]'(by decide +kernel)
theorem intervalAccepted0491 : candidateIntervalCheck candidate0491 (1547/10000) (1549/10000) piece0491=true := by decide +kernel
noncomputable def cell0491 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0491 accepted0491 (1547/10000) (1549/10000) piece0491
    intervalAccepted0491 (fun t => piece_le_psi ⟨451,by decide +kernel⟩ t)
def piece0492 : AffinePiece := pieces[452]'(by decide +kernel)
theorem intervalAccepted0492 : candidateIntervalCheck candidate0492 (1549/10000) (1551/10000) piece0492=true := by decide +kernel
noncomputable def cell0492 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0492 accepted0492 (1549/10000) (1551/10000) piece0492
    intervalAccepted0492 (fun t => piece_le_psi ⟨452,by decide +kernel⟩ t)
def piece0493 : AffinePiece := pieces[453]'(by decide +kernel)
theorem intervalAccepted0493 : candidateIntervalCheck candidate0493 (1551/10000) (1553/10000) piece0493=true := by decide +kernel
noncomputable def cell0493 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0493 accepted0493 (1551/10000) (1553/10000) piece0493
    intervalAccepted0493 (fun t => piece_le_psi ⟨453,by decide +kernel⟩ t)
def piece0494 : AffinePiece := pieces[454]'(by decide +kernel)
theorem intervalAccepted0494 : candidateIntervalCheck candidate0494 (1553/10000) (311/2000) piece0494=true := by decide +kernel
noncomputable def cell0494 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0494 accepted0494 (1553/10000) (311/2000) piece0494
    intervalAccepted0494 (fun t => piece_le_psi ⟨454,by decide +kernel⟩ t)
def piece0495 : AffinePiece := pieces[455]'(by decide +kernel)
theorem intervalAccepted0495 : candidateIntervalCheck candidate0495 (311/2000) (1557/10000) piece0495=true := by decide +kernel
noncomputable def cell0495 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0495 accepted0495 (311/2000) (1557/10000) piece0495
    intervalAccepted0495 (fun t => piece_le_psi ⟨455,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0480, cell0481, cell0482, cell0483, cell0484, cell0485, cell0486, cell0487, cell0488, cell0489, cell0490, cell0491, cell0492, cell0493, cell0494, cell0495]
theorem chainAccepted : spinCellChainCheck (61/400) (1557/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (61/400) (1557/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0030
