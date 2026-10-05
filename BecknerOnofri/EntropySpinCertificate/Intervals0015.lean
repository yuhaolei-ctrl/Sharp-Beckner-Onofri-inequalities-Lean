module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0015

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0015
open CandidateBatch0015 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0240 : AffinePiece := pieces[200]'(by decide +kernel)
theorem intervalAccepted0240 : candidateIntervalCheck candidate0240 (209/2000) (1047/10000) piece0240=true := by decide +kernel
noncomputable def cell0240 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0240 accepted0240 (209/2000) (1047/10000) piece0240
    intervalAccepted0240 (fun t => piece_le_psi ⟨200,by decide +kernel⟩ t)
def piece0241 : AffinePiece := pieces[201]'(by decide +kernel)
theorem intervalAccepted0241 : candidateIntervalCheck candidate0241 (1047/10000) (1049/10000) piece0241=true := by decide +kernel
noncomputable def cell0241 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0241 accepted0241 (1047/10000) (1049/10000) piece0241
    intervalAccepted0241 (fun t => piece_le_psi ⟨201,by decide +kernel⟩ t)
def piece0242 : AffinePiece := pieces[202]'(by decide +kernel)
theorem intervalAccepted0242 : candidateIntervalCheck candidate0242 (1049/10000) (1051/10000) piece0242=true := by decide +kernel
noncomputable def cell0242 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0242 accepted0242 (1049/10000) (1051/10000) piece0242
    intervalAccepted0242 (fun t => piece_le_psi ⟨202,by decide +kernel⟩ t)
def piece0243 : AffinePiece := pieces[203]'(by decide +kernel)
theorem intervalAccepted0243 : candidateIntervalCheck candidate0243 (1051/10000) (1053/10000) piece0243=true := by decide +kernel
noncomputable def cell0243 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0243 accepted0243 (1051/10000) (1053/10000) piece0243
    intervalAccepted0243 (fun t => piece_le_psi ⟨203,by decide +kernel⟩ t)
def piece0244 : AffinePiece := pieces[204]'(by decide +kernel)
theorem intervalAccepted0244 : candidateIntervalCheck candidate0244 (1053/10000) (211/2000) piece0244=true := by decide +kernel
noncomputable def cell0244 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0244 accepted0244 (1053/10000) (211/2000) piece0244
    intervalAccepted0244 (fun t => piece_le_psi ⟨204,by decide +kernel⟩ t)
def piece0245 : AffinePiece := pieces[205]'(by decide +kernel)
theorem intervalAccepted0245 : candidateIntervalCheck candidate0245 (211/2000) (1057/10000) piece0245=true := by decide +kernel
noncomputable def cell0245 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0245 accepted0245 (211/2000) (1057/10000) piece0245
    intervalAccepted0245 (fun t => piece_le_psi ⟨205,by decide +kernel⟩ t)
def piece0246 : AffinePiece := pieces[206]'(by decide +kernel)
theorem intervalAccepted0246 : candidateIntervalCheck candidate0246 (1057/10000) (1059/10000) piece0246=true := by decide +kernel
noncomputable def cell0246 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0246 accepted0246 (1057/10000) (1059/10000) piece0246
    intervalAccepted0246 (fun t => piece_le_psi ⟨206,by decide +kernel⟩ t)
def piece0247 : AffinePiece := pieces[207]'(by decide +kernel)
theorem intervalAccepted0247 : candidateIntervalCheck candidate0247 (1059/10000) (1061/10000) piece0247=true := by decide +kernel
noncomputable def cell0247 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0247 accepted0247 (1059/10000) (1061/10000) piece0247
    intervalAccepted0247 (fun t => piece_le_psi ⟨207,by decide +kernel⟩ t)
def piece0248 : AffinePiece := pieces[208]'(by decide +kernel)
theorem intervalAccepted0248 : candidateIntervalCheck candidate0248 (1061/10000) (1063/10000) piece0248=true := by decide +kernel
noncomputable def cell0248 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0248 accepted0248 (1061/10000) (1063/10000) piece0248
    intervalAccepted0248 (fun t => piece_le_psi ⟨208,by decide +kernel⟩ t)
def piece0249 : AffinePiece := pieces[209]'(by decide +kernel)
theorem intervalAccepted0249 : candidateIntervalCheck candidate0249 (1063/10000) (213/2000) piece0249=true := by decide +kernel
noncomputable def cell0249 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0249 accepted0249 (1063/10000) (213/2000) piece0249
    intervalAccepted0249 (fun t => piece_le_psi ⟨209,by decide +kernel⟩ t)
def piece0250 : AffinePiece := pieces[210]'(by decide +kernel)
theorem intervalAccepted0250 : candidateIntervalCheck candidate0250 (213/2000) (1067/10000) piece0250=true := by decide +kernel
noncomputable def cell0250 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0250 accepted0250 (213/2000) (1067/10000) piece0250
    intervalAccepted0250 (fun t => piece_le_psi ⟨210,by decide +kernel⟩ t)
def piece0251 : AffinePiece := pieces[211]'(by decide +kernel)
theorem intervalAccepted0251 : candidateIntervalCheck candidate0251 (1067/10000) (1069/10000) piece0251=true := by decide +kernel
noncomputable def cell0251 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0251 accepted0251 (1067/10000) (1069/10000) piece0251
    intervalAccepted0251 (fun t => piece_le_psi ⟨211,by decide +kernel⟩ t)
def piece0252 : AffinePiece := pieces[212]'(by decide +kernel)
theorem intervalAccepted0252 : candidateIntervalCheck candidate0252 (1069/10000) (1071/10000) piece0252=true := by decide +kernel
noncomputable def cell0252 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0252 accepted0252 (1069/10000) (1071/10000) piece0252
    intervalAccepted0252 (fun t => piece_le_psi ⟨212,by decide +kernel⟩ t)
def piece0253 : AffinePiece := pieces[213]'(by decide +kernel)
theorem intervalAccepted0253 : candidateIntervalCheck candidate0253 (1071/10000) (1073/10000) piece0253=true := by decide +kernel
noncomputable def cell0253 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0253 accepted0253 (1071/10000) (1073/10000) piece0253
    intervalAccepted0253 (fun t => piece_le_psi ⟨213,by decide +kernel⟩ t)
def piece0254 : AffinePiece := pieces[214]'(by decide +kernel)
theorem intervalAccepted0254 : candidateIntervalCheck candidate0254 (1073/10000) (43/400) piece0254=true := by decide +kernel
noncomputable def cell0254 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0254 accepted0254 (1073/10000) (43/400) piece0254
    intervalAccepted0254 (fun t => piece_le_psi ⟨214,by decide +kernel⟩ t)
def piece0255 : AffinePiece := pieces[215]'(by decide +kernel)
theorem intervalAccepted0255 : candidateIntervalCheck candidate0255 (43/400) (1077/10000) piece0255=true := by decide +kernel
noncomputable def cell0255 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0255 accepted0255 (43/400) (1077/10000) piece0255
    intervalAccepted0255 (fun t => piece_le_psi ⟨215,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0240, cell0241, cell0242, cell0243, cell0244, cell0245, cell0246, cell0247, cell0248, cell0249, cell0250, cell0251, cell0252, cell0253, cell0254, cell0255]
theorem chainAccepted : spinCellChainCheck (209/2000) (1077/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (209/2000) (1077/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0015
