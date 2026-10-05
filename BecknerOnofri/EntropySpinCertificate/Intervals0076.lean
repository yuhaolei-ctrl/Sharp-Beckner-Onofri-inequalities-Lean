import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0076
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0076
open CandidateBatch0076 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1216 : AffinePiece := pieces[1114]'(by decide +kernel)
theorem intervalAccepted1216 : candidateIntervalCheck candidate1216 (349/500) (699/1000) piece1216=true := by decide +kernel
noncomputable def cell1216 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1216 accepted1216 (349/500) (699/1000) piece1216
    intervalAccepted1216 (fun t => piece_le_psi ⟨1114,by decide +kernel⟩ t)
def piece1217 : AffinePiece := pieces[1115]'(by decide +kernel)
theorem intervalAccepted1217 : candidateIntervalCheck candidate1217 (699/1000) (7/10) piece1217=true := by decide +kernel
noncomputable def cell1217 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1217 accepted1217 (699/1000) (7/10) piece1217
    intervalAccepted1217 (fun t => piece_le_psi ⟨1115,by decide +kernel⟩ t)
def piece1218 : AffinePiece := pieces[1116]'(by decide +kernel)
theorem intervalAccepted1218 : candidateIntervalCheck candidate1218 (7/10) (701/1000) piece1218=true := by decide +kernel
noncomputable def cell1218 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1218 accepted1218 (7/10) (701/1000) piece1218
    intervalAccepted1218 (fun t => piece_le_psi ⟨1116,by decide +kernel⟩ t)
def piece1219 : AffinePiece := pieces[1117]'(by decide +kernel)
theorem intervalAccepted1219 : candidateIntervalCheck candidate1219 (701/1000) (351/500) piece1219=true := by decide +kernel
noncomputable def cell1219 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1219 accepted1219 (701/1000) (351/500) piece1219
    intervalAccepted1219 (fun t => piece_le_psi ⟨1117,by decide +kernel⟩ t)
def piece1220 : AffinePiece := pieces[1118]'(by decide +kernel)
theorem intervalAccepted1220 : candidateIntervalCheck candidate1220 (351/500) (703/1000) piece1220=true := by decide +kernel
noncomputable def cell1220 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1220 accepted1220 (351/500) (703/1000) piece1220
    intervalAccepted1220 (fun t => piece_le_psi ⟨1118,by decide +kernel⟩ t)
def piece1221 : AffinePiece := pieces[1119]'(by decide +kernel)
theorem intervalAccepted1221 : candidateIntervalCheck candidate1221 (703/1000) (88/125) piece1221=true := by decide +kernel
noncomputable def cell1221 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1221 accepted1221 (703/1000) (88/125) piece1221
    intervalAccepted1221 (fun t => piece_le_psi ⟨1119,by decide +kernel⟩ t)
def piece1222 : AffinePiece := pieces[1120]'(by decide +kernel)
theorem intervalAccepted1222 : candidateIntervalCheck candidate1222 (88/125) (141/200) piece1222=true := by decide +kernel
noncomputable def cell1222 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1222 accepted1222 (88/125) (141/200) piece1222
    intervalAccepted1222 (fun t => piece_le_psi ⟨1120,by decide +kernel⟩ t)
def piece1223 : AffinePiece := pieces[1121]'(by decide +kernel)
theorem intervalAccepted1223 : candidateIntervalCheck candidate1223 (141/200) (353/500) piece1223=true := by decide +kernel
noncomputable def cell1223 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1223 accepted1223 (141/200) (353/500) piece1223
    intervalAccepted1223 (fun t => piece_le_psi ⟨1121,by decide +kernel⟩ t)
def piece1224 : AffinePiece := pieces[1122]'(by decide +kernel)
theorem intervalAccepted1224 : candidateIntervalCheck candidate1224 (353/500) (707/1000) piece1224=true := by decide +kernel
noncomputable def cell1224 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1224 accepted1224 (353/500) (707/1000) piece1224
    intervalAccepted1224 (fun t => piece_le_psi ⟨1122,by decide +kernel⟩ t)
def piece1225 : AffinePiece := pieces[1123]'(by decide +kernel)
theorem intervalAccepted1225 : candidateIntervalCheck candidate1225 (707/1000) (177/250) piece1225=true := by decide +kernel
noncomputable def cell1225 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1225 accepted1225 (707/1000) (177/250) piece1225
    intervalAccepted1225 (fun t => piece_le_psi ⟨1123,by decide +kernel⟩ t)
def piece1226 : AffinePiece := pieces[1124]'(by decide +kernel)
theorem intervalAccepted1226 : candidateIntervalCheck candidate1226 (177/250) (709/1000) piece1226=true := by decide +kernel
noncomputable def cell1226 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1226 accepted1226 (177/250) (709/1000) piece1226
    intervalAccepted1226 (fun t => piece_le_psi ⟨1124,by decide +kernel⟩ t)
def piece1227 : AffinePiece := pieces[1125]'(by decide +kernel)
theorem intervalAccepted1227 : candidateIntervalCheck candidate1227 (709/1000) (71/100) piece1227=true := by decide +kernel
noncomputable def cell1227 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1227 accepted1227 (709/1000) (71/100) piece1227
    intervalAccepted1227 (fun t => piece_le_psi ⟨1125,by decide +kernel⟩ t)
def piece1228 : AffinePiece := pieces[1126]'(by decide +kernel)
theorem intervalAccepted1228 : candidateIntervalCheck candidate1228 (71/100) (711/1000) piece1228=true := by decide +kernel
noncomputable def cell1228 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1228 accepted1228 (71/100) (711/1000) piece1228
    intervalAccepted1228 (fun t => piece_le_psi ⟨1126,by decide +kernel⟩ t)
def piece1229 : AffinePiece := pieces[1127]'(by decide +kernel)
theorem intervalAccepted1229 : candidateIntervalCheck candidate1229 (711/1000) (89/125) piece1229=true := by decide +kernel
noncomputable def cell1229 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1229 accepted1229 (711/1000) (89/125) piece1229
    intervalAccepted1229 (fun t => piece_le_psi ⟨1127,by decide +kernel⟩ t)
def piece1230 : AffinePiece := pieces[1128]'(by decide +kernel)
theorem intervalAccepted1230 : candidateIntervalCheck candidate1230 (89/125) (713/1000) piece1230=true := by decide +kernel
noncomputable def cell1230 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1230 accepted1230 (89/125) (713/1000) piece1230
    intervalAccepted1230 (fun t => piece_le_psi ⟨1128,by decide +kernel⟩ t)
def piece1231 : AffinePiece := pieces[1129]'(by decide +kernel)
theorem intervalAccepted1231 : candidateIntervalCheck candidate1231 (713/1000) (357/500) piece1231=true := by decide +kernel
noncomputable def cell1231 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1231 accepted1231 (713/1000) (357/500) piece1231
    intervalAccepted1231 (fun t => piece_le_psi ⟨1129,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1216, cell1217, cell1218, cell1219, cell1220, cell1221, cell1222, cell1223, cell1224, cell1225, cell1226, cell1227, cell1228, cell1229, cell1230, cell1231]
theorem chainAccepted : spinCellChainCheck (349/500) (357/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (349/500) (357/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0076
