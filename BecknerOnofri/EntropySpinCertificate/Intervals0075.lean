module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0075

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0075
open CandidateBatch0075 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1200 : AffinePiece := pieces[1098]'(by decide +kernel)
theorem intervalAccepted1200 : candidateIntervalCheck candidate1200 (341/500) (683/1000) piece1200=true := by decide +kernel
noncomputable def cell1200 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1200 accepted1200 (341/500) (683/1000) piece1200
    intervalAccepted1200 (fun t => piece_le_psi ⟨1098,by decide +kernel⟩ t)
def piece1201 : AffinePiece := pieces[1099]'(by decide +kernel)
theorem intervalAccepted1201 : candidateIntervalCheck candidate1201 (683/1000) (171/250) piece1201=true := by decide +kernel
noncomputable def cell1201 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1201 accepted1201 (683/1000) (171/250) piece1201
    intervalAccepted1201 (fun t => piece_le_psi ⟨1099,by decide +kernel⟩ t)
def piece1202 : AffinePiece := pieces[1100]'(by decide +kernel)
theorem intervalAccepted1202 : candidateIntervalCheck candidate1202 (171/250) (137/200) piece1202=true := by decide +kernel
noncomputable def cell1202 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1202 accepted1202 (171/250) (137/200) piece1202
    intervalAccepted1202 (fun t => piece_le_psi ⟨1100,by decide +kernel⟩ t)
def piece1203 : AffinePiece := pieces[1101]'(by decide +kernel)
theorem intervalAccepted1203 : candidateIntervalCheck candidate1203 (137/200) (343/500) piece1203=true := by decide +kernel
noncomputable def cell1203 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1203 accepted1203 (137/200) (343/500) piece1203
    intervalAccepted1203 (fun t => piece_le_psi ⟨1101,by decide +kernel⟩ t)
def piece1204 : AffinePiece := pieces[1102]'(by decide +kernel)
theorem intervalAccepted1204 : candidateIntervalCheck candidate1204 (343/500) (687/1000) piece1204=true := by decide +kernel
noncomputable def cell1204 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1204 accepted1204 (343/500) (687/1000) piece1204
    intervalAccepted1204 (fun t => piece_le_psi ⟨1102,by decide +kernel⟩ t)
def piece1205 : AffinePiece := pieces[1103]'(by decide +kernel)
theorem intervalAccepted1205 : candidateIntervalCheck candidate1205 (687/1000) (86/125) piece1205=true := by decide +kernel
noncomputable def cell1205 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1205 accepted1205 (687/1000) (86/125) piece1205
    intervalAccepted1205 (fun t => piece_le_psi ⟨1103,by decide +kernel⟩ t)
def piece1206 : AffinePiece := pieces[1104]'(by decide +kernel)
theorem intervalAccepted1206 : candidateIntervalCheck candidate1206 (86/125) (689/1000) piece1206=true := by decide +kernel
noncomputable def cell1206 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1206 accepted1206 (86/125) (689/1000) piece1206
    intervalAccepted1206 (fun t => piece_le_psi ⟨1104,by decide +kernel⟩ t)
def piece1207 : AffinePiece := pieces[1105]'(by decide +kernel)
theorem intervalAccepted1207 : candidateIntervalCheck candidate1207 (689/1000) (69/100) piece1207=true := by decide +kernel
noncomputable def cell1207 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1207 accepted1207 (689/1000) (69/100) piece1207
    intervalAccepted1207 (fun t => piece_le_psi ⟨1105,by decide +kernel⟩ t)
def piece1208 : AffinePiece := pieces[1106]'(by decide +kernel)
theorem intervalAccepted1208 : candidateIntervalCheck candidate1208 (69/100) (691/1000) piece1208=true := by decide +kernel
noncomputable def cell1208 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1208 accepted1208 (69/100) (691/1000) piece1208
    intervalAccepted1208 (fun t => piece_le_psi ⟨1106,by decide +kernel⟩ t)
def piece1209 : AffinePiece := pieces[1107]'(by decide +kernel)
theorem intervalAccepted1209 : candidateIntervalCheck candidate1209 (691/1000) (173/250) piece1209=true := by decide +kernel
noncomputable def cell1209 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1209 accepted1209 (691/1000) (173/250) piece1209
    intervalAccepted1209 (fun t => piece_le_psi ⟨1107,by decide +kernel⟩ t)
def piece1210 : AffinePiece := pieces[1108]'(by decide +kernel)
theorem intervalAccepted1210 : candidateIntervalCheck candidate1210 (173/250) (693/1000) piece1210=true := by decide +kernel
noncomputable def cell1210 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1210 accepted1210 (173/250) (693/1000) piece1210
    intervalAccepted1210 (fun t => piece_le_psi ⟨1108,by decide +kernel⟩ t)
def piece1211 : AffinePiece := pieces[1109]'(by decide +kernel)
theorem intervalAccepted1211 : candidateIntervalCheck candidate1211 (693/1000) (347/500) piece1211=true := by decide +kernel
noncomputable def cell1211 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1211 accepted1211 (693/1000) (347/500) piece1211
    intervalAccepted1211 (fun t => piece_le_psi ⟨1109,by decide +kernel⟩ t)
def piece1212 : AffinePiece := pieces[1110]'(by decide +kernel)
theorem intervalAccepted1212 : candidateIntervalCheck candidate1212 (347/500) (139/200) piece1212=true := by decide +kernel
noncomputable def cell1212 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1212 accepted1212 (347/500) (139/200) piece1212
    intervalAccepted1212 (fun t => piece_le_psi ⟨1110,by decide +kernel⟩ t)
def piece1213 : AffinePiece := pieces[1111]'(by decide +kernel)
theorem intervalAccepted1213 : candidateIntervalCheck candidate1213 (139/200) (87/125) piece1213=true := by decide +kernel
noncomputable def cell1213 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1213 accepted1213 (139/200) (87/125) piece1213
    intervalAccepted1213 (fun t => piece_le_psi ⟨1111,by decide +kernel⟩ t)
def piece1214 : AffinePiece := pieces[1112]'(by decide +kernel)
theorem intervalAccepted1214 : candidateIntervalCheck candidate1214 (87/125) (697/1000) piece1214=true := by decide +kernel
noncomputable def cell1214 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1214 accepted1214 (87/125) (697/1000) piece1214
    intervalAccepted1214 (fun t => piece_le_psi ⟨1112,by decide +kernel⟩ t)
def piece1215 : AffinePiece := pieces[1113]'(by decide +kernel)
theorem intervalAccepted1215 : candidateIntervalCheck candidate1215 (697/1000) (349/500) piece1215=true := by decide +kernel
noncomputable def cell1215 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1215 accepted1215 (697/1000) (349/500) piece1215
    intervalAccepted1215 (fun t => piece_le_psi ⟨1113,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1200, cell1201, cell1202, cell1203, cell1204, cell1205, cell1206, cell1207, cell1208, cell1209, cell1210, cell1211, cell1212, cell1213, cell1214, cell1215]
theorem chainAccepted : spinCellChainCheck (341/500) (349/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (341/500) (349/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0075
