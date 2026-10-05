import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0018
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0018
open CandidateBatch0018 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0288 : AffinePiece := pieces[248]'(by decide +kernel)
theorem intervalAccepted0288 : candidateIntervalCheck candidate0288 (1141/10000) (1143/10000) piece0288=true := by decide +kernel
noncomputable def cell0288 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0288 accepted0288 (1141/10000) (1143/10000) piece0288
    intervalAccepted0288 (fun t => piece_le_psi ⟨248,by decide +kernel⟩ t)
def piece0289 : AffinePiece := pieces[249]'(by decide +kernel)
theorem intervalAccepted0289 : candidateIntervalCheck candidate0289 (1143/10000) (229/2000) piece0289=true := by decide +kernel
noncomputable def cell0289 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0289 accepted0289 (1143/10000) (229/2000) piece0289
    intervalAccepted0289 (fun t => piece_le_psi ⟨249,by decide +kernel⟩ t)
def piece0290 : AffinePiece := pieces[250]'(by decide +kernel)
theorem intervalAccepted0290 : candidateIntervalCheck candidate0290 (229/2000) (1147/10000) piece0290=true := by decide +kernel
noncomputable def cell0290 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0290 accepted0290 (229/2000) (1147/10000) piece0290
    intervalAccepted0290 (fun t => piece_le_psi ⟨250,by decide +kernel⟩ t)
def piece0291 : AffinePiece := pieces[251]'(by decide +kernel)
theorem intervalAccepted0291 : candidateIntervalCheck candidate0291 (1147/10000) (1149/10000) piece0291=true := by decide +kernel
noncomputable def cell0291 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0291 accepted0291 (1147/10000) (1149/10000) piece0291
    intervalAccepted0291 (fun t => piece_le_psi ⟨251,by decide +kernel⟩ t)
def piece0292 : AffinePiece := pieces[252]'(by decide +kernel)
theorem intervalAccepted0292 : candidateIntervalCheck candidate0292 (1149/10000) (1151/10000) piece0292=true := by decide +kernel
noncomputable def cell0292 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0292 accepted0292 (1149/10000) (1151/10000) piece0292
    intervalAccepted0292 (fun t => piece_le_psi ⟨252,by decide +kernel⟩ t)
def piece0293 : AffinePiece := pieces[253]'(by decide +kernel)
theorem intervalAccepted0293 : candidateIntervalCheck candidate0293 (1151/10000) (1153/10000) piece0293=true := by decide +kernel
noncomputable def cell0293 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0293 accepted0293 (1151/10000) (1153/10000) piece0293
    intervalAccepted0293 (fun t => piece_le_psi ⟨253,by decide +kernel⟩ t)
def piece0294 : AffinePiece := pieces[254]'(by decide +kernel)
theorem intervalAccepted0294 : candidateIntervalCheck candidate0294 (1153/10000) (231/2000) piece0294=true := by decide +kernel
noncomputable def cell0294 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0294 accepted0294 (1153/10000) (231/2000) piece0294
    intervalAccepted0294 (fun t => piece_le_psi ⟨254,by decide +kernel⟩ t)
def piece0295 : AffinePiece := pieces[255]'(by decide +kernel)
theorem intervalAccepted0295 : candidateIntervalCheck candidate0295 (231/2000) (1157/10000) piece0295=true := by decide +kernel
noncomputable def cell0295 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0295 accepted0295 (231/2000) (1157/10000) piece0295
    intervalAccepted0295 (fun t => piece_le_psi ⟨255,by decide +kernel⟩ t)
def piece0296 : AffinePiece := pieces[256]'(by decide +kernel)
theorem intervalAccepted0296 : candidateIntervalCheck candidate0296 (1157/10000) (1159/10000) piece0296=true := by decide +kernel
noncomputable def cell0296 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0296 accepted0296 (1157/10000) (1159/10000) piece0296
    intervalAccepted0296 (fun t => piece_le_psi ⟨256,by decide +kernel⟩ t)
def piece0297 : AffinePiece := pieces[257]'(by decide +kernel)
theorem intervalAccepted0297 : candidateIntervalCheck candidate0297 (1159/10000) (1161/10000) piece0297=true := by decide +kernel
noncomputable def cell0297 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0297 accepted0297 (1159/10000) (1161/10000) piece0297
    intervalAccepted0297 (fun t => piece_le_psi ⟨257,by decide +kernel⟩ t)
def piece0298 : AffinePiece := pieces[258]'(by decide +kernel)
theorem intervalAccepted0298 : candidateIntervalCheck candidate0298 (1161/10000) (1163/10000) piece0298=true := by decide +kernel
noncomputable def cell0298 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0298 accepted0298 (1161/10000) (1163/10000) piece0298
    intervalAccepted0298 (fun t => piece_le_psi ⟨258,by decide +kernel⟩ t)
def piece0299 : AffinePiece := pieces[259]'(by decide +kernel)
theorem intervalAccepted0299 : candidateIntervalCheck candidate0299 (1163/10000) (233/2000) piece0299=true := by decide +kernel
noncomputable def cell0299 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0299 accepted0299 (1163/10000) (233/2000) piece0299
    intervalAccepted0299 (fun t => piece_le_psi ⟨259,by decide +kernel⟩ t)
def piece0300 : AffinePiece := pieces[260]'(by decide +kernel)
theorem intervalAccepted0300 : candidateIntervalCheck candidate0300 (233/2000) (1167/10000) piece0300=true := by decide +kernel
noncomputable def cell0300 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0300 accepted0300 (233/2000) (1167/10000) piece0300
    intervalAccepted0300 (fun t => piece_le_psi ⟨260,by decide +kernel⟩ t)
def piece0301 : AffinePiece := pieces[261]'(by decide +kernel)
theorem intervalAccepted0301 : candidateIntervalCheck candidate0301 (1167/10000) (1169/10000) piece0301=true := by decide +kernel
noncomputable def cell0301 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0301 accepted0301 (1167/10000) (1169/10000) piece0301
    intervalAccepted0301 (fun t => piece_le_psi ⟨261,by decide +kernel⟩ t)
def piece0302 : AffinePiece := pieces[262]'(by decide +kernel)
theorem intervalAccepted0302 : candidateIntervalCheck candidate0302 (1169/10000) (1171/10000) piece0302=true := by decide +kernel
noncomputable def cell0302 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0302 accepted0302 (1169/10000) (1171/10000) piece0302
    intervalAccepted0302 (fun t => piece_le_psi ⟨262,by decide +kernel⟩ t)
def piece0303 : AffinePiece := pieces[263]'(by decide +kernel)
theorem intervalAccepted0303 : candidateIntervalCheck candidate0303 (1171/10000) (1173/10000) piece0303=true := by decide +kernel
noncomputable def cell0303 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0303 accepted0303 (1171/10000) (1173/10000) piece0303
    intervalAccepted0303 (fun t => piece_le_psi ⟨263,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0288, cell0289, cell0290, cell0291, cell0292, cell0293, cell0294, cell0295, cell0296, cell0297, cell0298, cell0299, cell0300, cell0301, cell0302, cell0303]
theorem chainAccepted : spinCellChainCheck (1141/10000) (1173/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1141/10000) (1173/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0018
