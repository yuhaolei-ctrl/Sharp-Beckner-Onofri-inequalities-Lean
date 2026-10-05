module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0024

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0024
open CandidateBatch0024 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0384 : AffinePiece := pieces[344]'(by decide +kernel)
theorem intervalAccepted0384 : candidateIntervalCheck candidate0384 (1333/10000) (267/2000) piece0384=true := by decide +kernel
noncomputable def cell0384 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0384 accepted0384 (1333/10000) (267/2000) piece0384
    intervalAccepted0384 (fun t => piece_le_psi ⟨344,by decide +kernel⟩ t)
def piece0385 : AffinePiece := pieces[345]'(by decide +kernel)
theorem intervalAccepted0385 : candidateIntervalCheck candidate0385 (267/2000) (1337/10000) piece0385=true := by decide +kernel
noncomputable def cell0385 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0385 accepted0385 (267/2000) (1337/10000) piece0385
    intervalAccepted0385 (fun t => piece_le_psi ⟨345,by decide +kernel⟩ t)
def piece0386 : AffinePiece := pieces[346]'(by decide +kernel)
theorem intervalAccepted0386 : candidateIntervalCheck candidate0386 (1337/10000) (1339/10000) piece0386=true := by decide +kernel
noncomputable def cell0386 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0386 accepted0386 (1337/10000) (1339/10000) piece0386
    intervalAccepted0386 (fun t => piece_le_psi ⟨346,by decide +kernel⟩ t)
def piece0387 : AffinePiece := pieces[347]'(by decide +kernel)
theorem intervalAccepted0387 : candidateIntervalCheck candidate0387 (1339/10000) (1341/10000) piece0387=true := by decide +kernel
noncomputable def cell0387 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0387 accepted0387 (1339/10000) (1341/10000) piece0387
    intervalAccepted0387 (fun t => piece_le_psi ⟨347,by decide +kernel⟩ t)
def piece0388 : AffinePiece := pieces[348]'(by decide +kernel)
theorem intervalAccepted0388 : candidateIntervalCheck candidate0388 (1341/10000) (1343/10000) piece0388=true := by decide +kernel
noncomputable def cell0388 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0388 accepted0388 (1341/10000) (1343/10000) piece0388
    intervalAccepted0388 (fun t => piece_le_psi ⟨348,by decide +kernel⟩ t)
def piece0389 : AffinePiece := pieces[349]'(by decide +kernel)
theorem intervalAccepted0389 : candidateIntervalCheck candidate0389 (1343/10000) (269/2000) piece0389=true := by decide +kernel
noncomputable def cell0389 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0389 accepted0389 (1343/10000) (269/2000) piece0389
    intervalAccepted0389 (fun t => piece_le_psi ⟨349,by decide +kernel⟩ t)
def piece0390 : AffinePiece := pieces[350]'(by decide +kernel)
theorem intervalAccepted0390 : candidateIntervalCheck candidate0390 (269/2000) (1347/10000) piece0390=true := by decide +kernel
noncomputable def cell0390 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0390 accepted0390 (269/2000) (1347/10000) piece0390
    intervalAccepted0390 (fun t => piece_le_psi ⟨350,by decide +kernel⟩ t)
def piece0391 : AffinePiece := pieces[351]'(by decide +kernel)
theorem intervalAccepted0391 : candidateIntervalCheck candidate0391 (1347/10000) (1349/10000) piece0391=true := by decide +kernel
noncomputable def cell0391 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0391 accepted0391 (1347/10000) (1349/10000) piece0391
    intervalAccepted0391 (fun t => piece_le_psi ⟨351,by decide +kernel⟩ t)
def piece0392 : AffinePiece := pieces[352]'(by decide +kernel)
theorem intervalAccepted0392 : candidateIntervalCheck candidate0392 (1349/10000) (1351/10000) piece0392=true := by decide +kernel
noncomputable def cell0392 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0392 accepted0392 (1349/10000) (1351/10000) piece0392
    intervalAccepted0392 (fun t => piece_le_psi ⟨352,by decide +kernel⟩ t)
def piece0393 : AffinePiece := pieces[353]'(by decide +kernel)
theorem intervalAccepted0393 : candidateIntervalCheck candidate0393 (1351/10000) (1353/10000) piece0393=true := by decide +kernel
noncomputable def cell0393 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0393 accepted0393 (1351/10000) (1353/10000) piece0393
    intervalAccepted0393 (fun t => piece_le_psi ⟨353,by decide +kernel⟩ t)
def piece0394 : AffinePiece := pieces[354]'(by decide +kernel)
theorem intervalAccepted0394 : candidateIntervalCheck candidate0394 (1353/10000) (271/2000) piece0394=true := by decide +kernel
noncomputable def cell0394 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0394 accepted0394 (1353/10000) (271/2000) piece0394
    intervalAccepted0394 (fun t => piece_le_psi ⟨354,by decide +kernel⟩ t)
def piece0395 : AffinePiece := pieces[355]'(by decide +kernel)
theorem intervalAccepted0395 : candidateIntervalCheck candidate0395 (271/2000) (1357/10000) piece0395=true := by decide +kernel
noncomputable def cell0395 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0395 accepted0395 (271/2000) (1357/10000) piece0395
    intervalAccepted0395 (fun t => piece_le_psi ⟨355,by decide +kernel⟩ t)
def piece0396 : AffinePiece := pieces[356]'(by decide +kernel)
theorem intervalAccepted0396 : candidateIntervalCheck candidate0396 (1357/10000) (1359/10000) piece0396=true := by decide +kernel
noncomputable def cell0396 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0396 accepted0396 (1357/10000) (1359/10000) piece0396
    intervalAccepted0396 (fun t => piece_le_psi ⟨356,by decide +kernel⟩ t)
def piece0397 : AffinePiece := pieces[357]'(by decide +kernel)
theorem intervalAccepted0397 : candidateIntervalCheck candidate0397 (1359/10000) (1361/10000) piece0397=true := by decide +kernel
noncomputable def cell0397 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0397 accepted0397 (1359/10000) (1361/10000) piece0397
    intervalAccepted0397 (fun t => piece_le_psi ⟨357,by decide +kernel⟩ t)
def piece0398 : AffinePiece := pieces[358]'(by decide +kernel)
theorem intervalAccepted0398 : candidateIntervalCheck candidate0398 (1361/10000) (1363/10000) piece0398=true := by decide +kernel
noncomputable def cell0398 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0398 accepted0398 (1361/10000) (1363/10000) piece0398
    intervalAccepted0398 (fun t => piece_le_psi ⟨358,by decide +kernel⟩ t)
def piece0399 : AffinePiece := pieces[359]'(by decide +kernel)
theorem intervalAccepted0399 : candidateIntervalCheck candidate0399 (1363/10000) (273/2000) piece0399=true := by decide +kernel
noncomputable def cell0399 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0399 accepted0399 (1363/10000) (273/2000) piece0399
    intervalAccepted0399 (fun t => piece_le_psi ⟨359,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0384, cell0385, cell0386, cell0387, cell0388, cell0389, cell0390, cell0391, cell0392, cell0393, cell0394, cell0395, cell0396, cell0397, cell0398, cell0399]
theorem chainAccepted : spinCellChainCheck (1333/10000) (273/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1333/10000) (273/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0024
