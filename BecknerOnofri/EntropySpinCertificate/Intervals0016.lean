import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0016
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0016
open CandidateBatch0016 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0256 : AffinePiece := pieces[216]'(by decide +kernel)
theorem intervalAccepted0256 : candidateIntervalCheck candidate0256 (1077/10000) (1079/10000) piece0256=true := by decide +kernel
noncomputable def cell0256 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0256 accepted0256 (1077/10000) (1079/10000) piece0256
    intervalAccepted0256 (fun t => piece_le_psi ⟨216,by decide +kernel⟩ t)
def piece0257 : AffinePiece := pieces[217]'(by decide +kernel)
theorem intervalAccepted0257 : candidateIntervalCheck candidate0257 (1079/10000) (1081/10000) piece0257=true := by decide +kernel
noncomputable def cell0257 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0257 accepted0257 (1079/10000) (1081/10000) piece0257
    intervalAccepted0257 (fun t => piece_le_psi ⟨217,by decide +kernel⟩ t)
def piece0258 : AffinePiece := pieces[218]'(by decide +kernel)
theorem intervalAccepted0258 : candidateIntervalCheck candidate0258 (1081/10000) (1083/10000) piece0258=true := by decide +kernel
noncomputable def cell0258 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0258 accepted0258 (1081/10000) (1083/10000) piece0258
    intervalAccepted0258 (fun t => piece_le_psi ⟨218,by decide +kernel⟩ t)
def piece0259 : AffinePiece := pieces[219]'(by decide +kernel)
theorem intervalAccepted0259 : candidateIntervalCheck candidate0259 (1083/10000) (217/2000) piece0259=true := by decide +kernel
noncomputable def cell0259 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0259 accepted0259 (1083/10000) (217/2000) piece0259
    intervalAccepted0259 (fun t => piece_le_psi ⟨219,by decide +kernel⟩ t)
def piece0260 : AffinePiece := pieces[220]'(by decide +kernel)
theorem intervalAccepted0260 : candidateIntervalCheck candidate0260 (217/2000) (1087/10000) piece0260=true := by decide +kernel
noncomputable def cell0260 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0260 accepted0260 (217/2000) (1087/10000) piece0260
    intervalAccepted0260 (fun t => piece_le_psi ⟨220,by decide +kernel⟩ t)
def piece0261 : AffinePiece := pieces[221]'(by decide +kernel)
theorem intervalAccepted0261 : candidateIntervalCheck candidate0261 (1087/10000) (1089/10000) piece0261=true := by decide +kernel
noncomputable def cell0261 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0261 accepted0261 (1087/10000) (1089/10000) piece0261
    intervalAccepted0261 (fun t => piece_le_psi ⟨221,by decide +kernel⟩ t)
def piece0262 : AffinePiece := pieces[222]'(by decide +kernel)
theorem intervalAccepted0262 : candidateIntervalCheck candidate0262 (1089/10000) (1091/10000) piece0262=true := by decide +kernel
noncomputable def cell0262 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0262 accepted0262 (1089/10000) (1091/10000) piece0262
    intervalAccepted0262 (fun t => piece_le_psi ⟨222,by decide +kernel⟩ t)
def piece0263 : AffinePiece := pieces[223]'(by decide +kernel)
theorem intervalAccepted0263 : candidateIntervalCheck candidate0263 (1091/10000) (1093/10000) piece0263=true := by decide +kernel
noncomputable def cell0263 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0263 accepted0263 (1091/10000) (1093/10000) piece0263
    intervalAccepted0263 (fun t => piece_le_psi ⟨223,by decide +kernel⟩ t)
def piece0264 : AffinePiece := pieces[224]'(by decide +kernel)
theorem intervalAccepted0264 : candidateIntervalCheck candidate0264 (1093/10000) (219/2000) piece0264=true := by decide +kernel
noncomputable def cell0264 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0264 accepted0264 (1093/10000) (219/2000) piece0264
    intervalAccepted0264 (fun t => piece_le_psi ⟨224,by decide +kernel⟩ t)
def piece0265 : AffinePiece := pieces[225]'(by decide +kernel)
theorem intervalAccepted0265 : candidateIntervalCheck candidate0265 (219/2000) (1097/10000) piece0265=true := by decide +kernel
noncomputable def cell0265 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0265 accepted0265 (219/2000) (1097/10000) piece0265
    intervalAccepted0265 (fun t => piece_le_psi ⟨225,by decide +kernel⟩ t)
def piece0266 : AffinePiece := pieces[226]'(by decide +kernel)
theorem intervalAccepted0266 : candidateIntervalCheck candidate0266 (1097/10000) (1099/10000) piece0266=true := by decide +kernel
noncomputable def cell0266 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0266 accepted0266 (1097/10000) (1099/10000) piece0266
    intervalAccepted0266 (fun t => piece_le_psi ⟨226,by decide +kernel⟩ t)
def piece0267 : AffinePiece := pieces[227]'(by decide +kernel)
theorem intervalAccepted0267 : candidateIntervalCheck candidate0267 (1099/10000) (1101/10000) piece0267=true := by decide +kernel
noncomputable def cell0267 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0267 accepted0267 (1099/10000) (1101/10000) piece0267
    intervalAccepted0267 (fun t => piece_le_psi ⟨227,by decide +kernel⟩ t)
def piece0268 : AffinePiece := pieces[228]'(by decide +kernel)
theorem intervalAccepted0268 : candidateIntervalCheck candidate0268 (1101/10000) (1103/10000) piece0268=true := by decide +kernel
noncomputable def cell0268 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0268 accepted0268 (1101/10000) (1103/10000) piece0268
    intervalAccepted0268 (fun t => piece_le_psi ⟨228,by decide +kernel⟩ t)
def piece0269 : AffinePiece := pieces[229]'(by decide +kernel)
theorem intervalAccepted0269 : candidateIntervalCheck candidate0269 (1103/10000) (221/2000) piece0269=true := by decide +kernel
noncomputable def cell0269 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0269 accepted0269 (1103/10000) (221/2000) piece0269
    intervalAccepted0269 (fun t => piece_le_psi ⟨229,by decide +kernel⟩ t)
def piece0270 : AffinePiece := pieces[230]'(by decide +kernel)
theorem intervalAccepted0270 : candidateIntervalCheck candidate0270 (221/2000) (1107/10000) piece0270=true := by decide +kernel
noncomputable def cell0270 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0270 accepted0270 (221/2000) (1107/10000) piece0270
    intervalAccepted0270 (fun t => piece_le_psi ⟨230,by decide +kernel⟩ t)
def piece0271 : AffinePiece := pieces[231]'(by decide +kernel)
theorem intervalAccepted0271 : candidateIntervalCheck candidate0271 (1107/10000) (1109/10000) piece0271=true := by decide +kernel
noncomputable def cell0271 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0271 accepted0271 (1107/10000) (1109/10000) piece0271
    intervalAccepted0271 (fun t => piece_le_psi ⟨231,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0256, cell0257, cell0258, cell0259, cell0260, cell0261, cell0262, cell0263, cell0264, cell0265, cell0266, cell0267, cell0268, cell0269, cell0270, cell0271]
theorem chainAccepted : spinCellChainCheck (1077/10000) (1109/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1077/10000) (1109/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0016
