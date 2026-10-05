import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0022
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0022
open CandidateBatch0022 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0352 : AffinePiece := pieces[312]'(by decide +kernel)
theorem intervalAccepted0352 : candidateIntervalCheck candidate0352 (1269/10000) (1271/10000) piece0352=true := by decide +kernel
noncomputable def cell0352 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0352 accepted0352 (1269/10000) (1271/10000) piece0352
    intervalAccepted0352 (fun t => piece_le_psi ⟨312,by decide +kernel⟩ t)
def piece0353 : AffinePiece := pieces[313]'(by decide +kernel)
theorem intervalAccepted0353 : candidateIntervalCheck candidate0353 (1271/10000) (1273/10000) piece0353=true := by decide +kernel
noncomputable def cell0353 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0353 accepted0353 (1271/10000) (1273/10000) piece0353
    intervalAccepted0353 (fun t => piece_le_psi ⟨313,by decide +kernel⟩ t)
def piece0354 : AffinePiece := pieces[314]'(by decide +kernel)
theorem intervalAccepted0354 : candidateIntervalCheck candidate0354 (1273/10000) (51/400) piece0354=true := by decide +kernel
noncomputable def cell0354 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0354 accepted0354 (1273/10000) (51/400) piece0354
    intervalAccepted0354 (fun t => piece_le_psi ⟨314,by decide +kernel⟩ t)
def piece0355 : AffinePiece := pieces[315]'(by decide +kernel)
theorem intervalAccepted0355 : candidateIntervalCheck candidate0355 (51/400) (1277/10000) piece0355=true := by decide +kernel
noncomputable def cell0355 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0355 accepted0355 (51/400) (1277/10000) piece0355
    intervalAccepted0355 (fun t => piece_le_psi ⟨315,by decide +kernel⟩ t)
def piece0356 : AffinePiece := pieces[316]'(by decide +kernel)
theorem intervalAccepted0356 : candidateIntervalCheck candidate0356 (1277/10000) (1279/10000) piece0356=true := by decide +kernel
noncomputable def cell0356 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0356 accepted0356 (1277/10000) (1279/10000) piece0356
    intervalAccepted0356 (fun t => piece_le_psi ⟨316,by decide +kernel⟩ t)
def piece0357 : AffinePiece := pieces[317]'(by decide +kernel)
theorem intervalAccepted0357 : candidateIntervalCheck candidate0357 (1279/10000) (1281/10000) piece0357=true := by decide +kernel
noncomputable def cell0357 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0357 accepted0357 (1279/10000) (1281/10000) piece0357
    intervalAccepted0357 (fun t => piece_le_psi ⟨317,by decide +kernel⟩ t)
def piece0358 : AffinePiece := pieces[318]'(by decide +kernel)
theorem intervalAccepted0358 : candidateIntervalCheck candidate0358 (1281/10000) (1283/10000) piece0358=true := by decide +kernel
noncomputable def cell0358 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0358 accepted0358 (1281/10000) (1283/10000) piece0358
    intervalAccepted0358 (fun t => piece_le_psi ⟨318,by decide +kernel⟩ t)
def piece0359 : AffinePiece := pieces[319]'(by decide +kernel)
theorem intervalAccepted0359 : candidateIntervalCheck candidate0359 (1283/10000) (257/2000) piece0359=true := by decide +kernel
noncomputable def cell0359 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0359 accepted0359 (1283/10000) (257/2000) piece0359
    intervalAccepted0359 (fun t => piece_le_psi ⟨319,by decide +kernel⟩ t)
def piece0360 : AffinePiece := pieces[320]'(by decide +kernel)
theorem intervalAccepted0360 : candidateIntervalCheck candidate0360 (257/2000) (1287/10000) piece0360=true := by decide +kernel
noncomputable def cell0360 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0360 accepted0360 (257/2000) (1287/10000) piece0360
    intervalAccepted0360 (fun t => piece_le_psi ⟨320,by decide +kernel⟩ t)
def piece0361 : AffinePiece := pieces[321]'(by decide +kernel)
theorem intervalAccepted0361 : candidateIntervalCheck candidate0361 (1287/10000) (1289/10000) piece0361=true := by decide +kernel
noncomputable def cell0361 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0361 accepted0361 (1287/10000) (1289/10000) piece0361
    intervalAccepted0361 (fun t => piece_le_psi ⟨321,by decide +kernel⟩ t)
def piece0362 : AffinePiece := pieces[322]'(by decide +kernel)
theorem intervalAccepted0362 : candidateIntervalCheck candidate0362 (1289/10000) (1291/10000) piece0362=true := by decide +kernel
noncomputable def cell0362 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0362 accepted0362 (1289/10000) (1291/10000) piece0362
    intervalAccepted0362 (fun t => piece_le_psi ⟨322,by decide +kernel⟩ t)
def piece0363 : AffinePiece := pieces[323]'(by decide +kernel)
theorem intervalAccepted0363 : candidateIntervalCheck candidate0363 (1291/10000) (1293/10000) piece0363=true := by decide +kernel
noncomputable def cell0363 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0363 accepted0363 (1291/10000) (1293/10000) piece0363
    intervalAccepted0363 (fun t => piece_le_psi ⟨323,by decide +kernel⟩ t)
def piece0364 : AffinePiece := pieces[324]'(by decide +kernel)
theorem intervalAccepted0364 : candidateIntervalCheck candidate0364 (1293/10000) (259/2000) piece0364=true := by decide +kernel
noncomputable def cell0364 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0364 accepted0364 (1293/10000) (259/2000) piece0364
    intervalAccepted0364 (fun t => piece_le_psi ⟨324,by decide +kernel⟩ t)
def piece0365 : AffinePiece := pieces[325]'(by decide +kernel)
theorem intervalAccepted0365 : candidateIntervalCheck candidate0365 (259/2000) (1297/10000) piece0365=true := by decide +kernel
noncomputable def cell0365 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0365 accepted0365 (259/2000) (1297/10000) piece0365
    intervalAccepted0365 (fun t => piece_le_psi ⟨325,by decide +kernel⟩ t)
def piece0366 : AffinePiece := pieces[326]'(by decide +kernel)
theorem intervalAccepted0366 : candidateIntervalCheck candidate0366 (1297/10000) (1299/10000) piece0366=true := by decide +kernel
noncomputable def cell0366 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0366 accepted0366 (1297/10000) (1299/10000) piece0366
    intervalAccepted0366 (fun t => piece_le_psi ⟨326,by decide +kernel⟩ t)
def piece0367 : AffinePiece := pieces[327]'(by decide +kernel)
theorem intervalAccepted0367 : candidateIntervalCheck candidate0367 (1299/10000) (1301/10000) piece0367=true := by decide +kernel
noncomputable def cell0367 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0367 accepted0367 (1299/10000) (1301/10000) piece0367
    intervalAccepted0367 (fun t => piece_le_psi ⟨327,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0352, cell0353, cell0354, cell0355, cell0356, cell0357, cell0358, cell0359, cell0360, cell0361, cell0362, cell0363, cell0364, cell0365, cell0366, cell0367]
theorem chainAccepted : spinCellChainCheck (1269/10000) (1301/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1269/10000) (1301/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0022
