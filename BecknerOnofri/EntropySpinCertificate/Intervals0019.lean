import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0019
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0019
open CandidateBatch0019 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0304 : AffinePiece := pieces[264]'(by decide +kernel)
theorem intervalAccepted0304 : candidateIntervalCheck candidate0304 (1173/10000) (47/400) piece0304=true := by decide +kernel
noncomputable def cell0304 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0304 accepted0304 (1173/10000) (47/400) piece0304
    intervalAccepted0304 (fun t => piece_le_psi ⟨264,by decide +kernel⟩ t)
def piece0305 : AffinePiece := pieces[265]'(by decide +kernel)
theorem intervalAccepted0305 : candidateIntervalCheck candidate0305 (47/400) (1177/10000) piece0305=true := by decide +kernel
noncomputable def cell0305 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0305 accepted0305 (47/400) (1177/10000) piece0305
    intervalAccepted0305 (fun t => piece_le_psi ⟨265,by decide +kernel⟩ t)
def piece0306 : AffinePiece := pieces[266]'(by decide +kernel)
theorem intervalAccepted0306 : candidateIntervalCheck candidate0306 (1177/10000) (1179/10000) piece0306=true := by decide +kernel
noncomputable def cell0306 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0306 accepted0306 (1177/10000) (1179/10000) piece0306
    intervalAccepted0306 (fun t => piece_le_psi ⟨266,by decide +kernel⟩ t)
def piece0307 : AffinePiece := pieces[267]'(by decide +kernel)
theorem intervalAccepted0307 : candidateIntervalCheck candidate0307 (1179/10000) (1181/10000) piece0307=true := by decide +kernel
noncomputable def cell0307 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0307 accepted0307 (1179/10000) (1181/10000) piece0307
    intervalAccepted0307 (fun t => piece_le_psi ⟨267,by decide +kernel⟩ t)
def piece0308 : AffinePiece := pieces[268]'(by decide +kernel)
theorem intervalAccepted0308 : candidateIntervalCheck candidate0308 (1181/10000) (1183/10000) piece0308=true := by decide +kernel
noncomputable def cell0308 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0308 accepted0308 (1181/10000) (1183/10000) piece0308
    intervalAccepted0308 (fun t => piece_le_psi ⟨268,by decide +kernel⟩ t)
def piece0309 : AffinePiece := pieces[269]'(by decide +kernel)
theorem intervalAccepted0309 : candidateIntervalCheck candidate0309 (1183/10000) (237/2000) piece0309=true := by decide +kernel
noncomputable def cell0309 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0309 accepted0309 (1183/10000) (237/2000) piece0309
    intervalAccepted0309 (fun t => piece_le_psi ⟨269,by decide +kernel⟩ t)
def piece0310 : AffinePiece := pieces[270]'(by decide +kernel)
theorem intervalAccepted0310 : candidateIntervalCheck candidate0310 (237/2000) (1187/10000) piece0310=true := by decide +kernel
noncomputable def cell0310 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0310 accepted0310 (237/2000) (1187/10000) piece0310
    intervalAccepted0310 (fun t => piece_le_psi ⟨270,by decide +kernel⟩ t)
def piece0311 : AffinePiece := pieces[271]'(by decide +kernel)
theorem intervalAccepted0311 : candidateIntervalCheck candidate0311 (1187/10000) (1189/10000) piece0311=true := by decide +kernel
noncomputable def cell0311 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0311 accepted0311 (1187/10000) (1189/10000) piece0311
    intervalAccepted0311 (fun t => piece_le_psi ⟨271,by decide +kernel⟩ t)
def piece0312 : AffinePiece := pieces[272]'(by decide +kernel)
theorem intervalAccepted0312 : candidateIntervalCheck candidate0312 (1189/10000) (1191/10000) piece0312=true := by decide +kernel
noncomputable def cell0312 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0312 accepted0312 (1189/10000) (1191/10000) piece0312
    intervalAccepted0312 (fun t => piece_le_psi ⟨272,by decide +kernel⟩ t)
def piece0313 : AffinePiece := pieces[273]'(by decide +kernel)
theorem intervalAccepted0313 : candidateIntervalCheck candidate0313 (1191/10000) (1193/10000) piece0313=true := by decide +kernel
noncomputable def cell0313 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0313 accepted0313 (1191/10000) (1193/10000) piece0313
    intervalAccepted0313 (fun t => piece_le_psi ⟨273,by decide +kernel⟩ t)
def piece0314 : AffinePiece := pieces[274]'(by decide +kernel)
theorem intervalAccepted0314 : candidateIntervalCheck candidate0314 (1193/10000) (239/2000) piece0314=true := by decide +kernel
noncomputable def cell0314 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0314 accepted0314 (1193/10000) (239/2000) piece0314
    intervalAccepted0314 (fun t => piece_le_psi ⟨274,by decide +kernel⟩ t)
def piece0315 : AffinePiece := pieces[275]'(by decide +kernel)
theorem intervalAccepted0315 : candidateIntervalCheck candidate0315 (239/2000) (1197/10000) piece0315=true := by decide +kernel
noncomputable def cell0315 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0315 accepted0315 (239/2000) (1197/10000) piece0315
    intervalAccepted0315 (fun t => piece_le_psi ⟨275,by decide +kernel⟩ t)
def piece0316 : AffinePiece := pieces[276]'(by decide +kernel)
theorem intervalAccepted0316 : candidateIntervalCheck candidate0316 (1197/10000) (1199/10000) piece0316=true := by decide +kernel
noncomputable def cell0316 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0316 accepted0316 (1197/10000) (1199/10000) piece0316
    intervalAccepted0316 (fun t => piece_le_psi ⟨276,by decide +kernel⟩ t)
def piece0317 : AffinePiece := pieces[277]'(by decide +kernel)
theorem intervalAccepted0317 : candidateIntervalCheck candidate0317 (1199/10000) (1201/10000) piece0317=true := by decide +kernel
noncomputable def cell0317 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0317 accepted0317 (1199/10000) (1201/10000) piece0317
    intervalAccepted0317 (fun t => piece_le_psi ⟨277,by decide +kernel⟩ t)
def piece0318 : AffinePiece := pieces[278]'(by decide +kernel)
theorem intervalAccepted0318 : candidateIntervalCheck candidate0318 (1201/10000) (1203/10000) piece0318=true := by decide +kernel
noncomputable def cell0318 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0318 accepted0318 (1201/10000) (1203/10000) piece0318
    intervalAccepted0318 (fun t => piece_le_psi ⟨278,by decide +kernel⟩ t)
def piece0319 : AffinePiece := pieces[279]'(by decide +kernel)
theorem intervalAccepted0319 : candidateIntervalCheck candidate0319 (1203/10000) (241/2000) piece0319=true := by decide +kernel
noncomputable def cell0319 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0319 accepted0319 (1203/10000) (241/2000) piece0319
    intervalAccepted0319 (fun t => piece_le_psi ⟨279,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0304, cell0305, cell0306, cell0307, cell0308, cell0309, cell0310, cell0311, cell0312, cell0313, cell0314, cell0315, cell0316, cell0317, cell0318, cell0319]
theorem chainAccepted : spinCellChainCheck (1173/10000) (241/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1173/10000) (241/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0019
