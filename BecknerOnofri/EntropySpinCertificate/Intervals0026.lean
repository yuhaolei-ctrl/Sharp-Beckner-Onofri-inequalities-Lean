import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0026
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0026
open CandidateBatch0026 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0416 : AffinePiece := pieces[376]'(by decide +kernel)
theorem intervalAccepted0416 : candidateIntervalCheck candidate0416 (1397/10000) (1399/10000) piece0416=true := by decide +kernel
noncomputable def cell0416 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0416 accepted0416 (1397/10000) (1399/10000) piece0416
    intervalAccepted0416 (fun t => piece_le_psi ⟨376,by decide +kernel⟩ t)
def piece0417 : AffinePiece := pieces[377]'(by decide +kernel)
theorem intervalAccepted0417 : candidateIntervalCheck candidate0417 (1399/10000) (1401/10000) piece0417=true := by decide +kernel
noncomputable def cell0417 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0417 accepted0417 (1399/10000) (1401/10000) piece0417
    intervalAccepted0417 (fun t => piece_le_psi ⟨377,by decide +kernel⟩ t)
def piece0418 : AffinePiece := pieces[378]'(by decide +kernel)
theorem intervalAccepted0418 : candidateIntervalCheck candidate0418 (1401/10000) (1403/10000) piece0418=true := by decide +kernel
noncomputable def cell0418 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0418 accepted0418 (1401/10000) (1403/10000) piece0418
    intervalAccepted0418 (fun t => piece_le_psi ⟨378,by decide +kernel⟩ t)
def piece0419 : AffinePiece := pieces[379]'(by decide +kernel)
theorem intervalAccepted0419 : candidateIntervalCheck candidate0419 (1403/10000) (281/2000) piece0419=true := by decide +kernel
noncomputable def cell0419 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0419 accepted0419 (1403/10000) (281/2000) piece0419
    intervalAccepted0419 (fun t => piece_le_psi ⟨379,by decide +kernel⟩ t)
def piece0420 : AffinePiece := pieces[380]'(by decide +kernel)
theorem intervalAccepted0420 : candidateIntervalCheck candidate0420 (281/2000) (1407/10000) piece0420=true := by decide +kernel
noncomputable def cell0420 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0420 accepted0420 (281/2000) (1407/10000) piece0420
    intervalAccepted0420 (fun t => piece_le_psi ⟨380,by decide +kernel⟩ t)
def piece0421 : AffinePiece := pieces[381]'(by decide +kernel)
theorem intervalAccepted0421 : candidateIntervalCheck candidate0421 (1407/10000) (1409/10000) piece0421=true := by decide +kernel
noncomputable def cell0421 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0421 accepted0421 (1407/10000) (1409/10000) piece0421
    intervalAccepted0421 (fun t => piece_le_psi ⟨381,by decide +kernel⟩ t)
def piece0422 : AffinePiece := pieces[382]'(by decide +kernel)
theorem intervalAccepted0422 : candidateIntervalCheck candidate0422 (1409/10000) (1411/10000) piece0422=true := by decide +kernel
noncomputable def cell0422 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0422 accepted0422 (1409/10000) (1411/10000) piece0422
    intervalAccepted0422 (fun t => piece_le_psi ⟨382,by decide +kernel⟩ t)
def piece0423 : AffinePiece := pieces[383]'(by decide +kernel)
theorem intervalAccepted0423 : candidateIntervalCheck candidate0423 (1411/10000) (1413/10000) piece0423=true := by decide +kernel
noncomputable def cell0423 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0423 accepted0423 (1411/10000) (1413/10000) piece0423
    intervalAccepted0423 (fun t => piece_le_psi ⟨383,by decide +kernel⟩ t)
def piece0424 : AffinePiece := pieces[384]'(by decide +kernel)
theorem intervalAccepted0424 : candidateIntervalCheck candidate0424 (1413/10000) (283/2000) piece0424=true := by decide +kernel
noncomputable def cell0424 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0424 accepted0424 (1413/10000) (283/2000) piece0424
    intervalAccepted0424 (fun t => piece_le_psi ⟨384,by decide +kernel⟩ t)
def piece0425 : AffinePiece := pieces[385]'(by decide +kernel)
theorem intervalAccepted0425 : candidateIntervalCheck candidate0425 (283/2000) (1417/10000) piece0425=true := by decide +kernel
noncomputable def cell0425 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0425 accepted0425 (283/2000) (1417/10000) piece0425
    intervalAccepted0425 (fun t => piece_le_psi ⟨385,by decide +kernel⟩ t)
def piece0426 : AffinePiece := pieces[386]'(by decide +kernel)
theorem intervalAccepted0426 : candidateIntervalCheck candidate0426 (1417/10000) (1419/10000) piece0426=true := by decide +kernel
noncomputable def cell0426 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0426 accepted0426 (1417/10000) (1419/10000) piece0426
    intervalAccepted0426 (fun t => piece_le_psi ⟨386,by decide +kernel⟩ t)
def piece0427 : AffinePiece := pieces[387]'(by decide +kernel)
theorem intervalAccepted0427 : candidateIntervalCheck candidate0427 (1419/10000) (1421/10000) piece0427=true := by decide +kernel
noncomputable def cell0427 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0427 accepted0427 (1419/10000) (1421/10000) piece0427
    intervalAccepted0427 (fun t => piece_le_psi ⟨387,by decide +kernel⟩ t)
def piece0428 : AffinePiece := pieces[388]'(by decide +kernel)
theorem intervalAccepted0428 : candidateIntervalCheck candidate0428 (1421/10000) (1423/10000) piece0428=true := by decide +kernel
noncomputable def cell0428 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0428 accepted0428 (1421/10000) (1423/10000) piece0428
    intervalAccepted0428 (fun t => piece_le_psi ⟨388,by decide +kernel⟩ t)
def piece0429 : AffinePiece := pieces[389]'(by decide +kernel)
theorem intervalAccepted0429 : candidateIntervalCheck candidate0429 (1423/10000) (57/400) piece0429=true := by decide +kernel
noncomputable def cell0429 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0429 accepted0429 (1423/10000) (57/400) piece0429
    intervalAccepted0429 (fun t => piece_le_psi ⟨389,by decide +kernel⟩ t)
def piece0430 : AffinePiece := pieces[390]'(by decide +kernel)
theorem intervalAccepted0430 : candidateIntervalCheck candidate0430 (57/400) (1427/10000) piece0430=true := by decide +kernel
noncomputable def cell0430 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0430 accepted0430 (57/400) (1427/10000) piece0430
    intervalAccepted0430 (fun t => piece_le_psi ⟨390,by decide +kernel⟩ t)
def piece0431 : AffinePiece := pieces[391]'(by decide +kernel)
theorem intervalAccepted0431 : candidateIntervalCheck candidate0431 (1427/10000) (1429/10000) piece0431=true := by decide +kernel
noncomputable def cell0431 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0431 accepted0431 (1427/10000) (1429/10000) piece0431
    intervalAccepted0431 (fun t => piece_le_psi ⟨391,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0416, cell0417, cell0418, cell0419, cell0420, cell0421, cell0422, cell0423, cell0424, cell0425, cell0426, cell0427, cell0428, cell0429, cell0430, cell0431]
theorem chainAccepted : spinCellChainCheck (1397/10000) (1429/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1397/10000) (1429/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0026
