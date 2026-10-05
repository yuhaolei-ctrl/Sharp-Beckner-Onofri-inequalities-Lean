import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0071
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0071
open CandidateBatch0071 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1136 : AffinePiece := pieces[1034]'(by decide +kernel)
theorem intervalAccepted1136 : candidateIntervalCheck candidate1136 (309/500) (619/1000) piece1136=true := by decide +kernel
noncomputable def cell1136 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1136 accepted1136 (309/500) (619/1000) piece1136
    intervalAccepted1136 (fun t => piece_le_psi ⟨1034,by decide +kernel⟩ t)
def piece1137 : AffinePiece := pieces[1035]'(by decide +kernel)
theorem intervalAccepted1137 : candidateIntervalCheck candidate1137 (619/1000) (31/50) piece1137=true := by decide +kernel
noncomputable def cell1137 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1137 accepted1137 (619/1000) (31/50) piece1137
    intervalAccepted1137 (fun t => piece_le_psi ⟨1035,by decide +kernel⟩ t)
def piece1138 : AffinePiece := pieces[1036]'(by decide +kernel)
theorem intervalAccepted1138 : candidateIntervalCheck candidate1138 (31/50) (621/1000) piece1138=true := by decide +kernel
noncomputable def cell1138 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1138 accepted1138 (31/50) (621/1000) piece1138
    intervalAccepted1138 (fun t => piece_le_psi ⟨1036,by decide +kernel⟩ t)
def piece1139 : AffinePiece := pieces[1037]'(by decide +kernel)
theorem intervalAccepted1139 : candidateIntervalCheck candidate1139 (621/1000) (311/500) piece1139=true := by decide +kernel
noncomputable def cell1139 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1139 accepted1139 (621/1000) (311/500) piece1139
    intervalAccepted1139 (fun t => piece_le_psi ⟨1037,by decide +kernel⟩ t)
def piece1140 : AffinePiece := pieces[1038]'(by decide +kernel)
theorem intervalAccepted1140 : candidateIntervalCheck candidate1140 (311/500) (623/1000) piece1140=true := by decide +kernel
noncomputable def cell1140 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1140 accepted1140 (311/500) (623/1000) piece1140
    intervalAccepted1140 (fun t => piece_le_psi ⟨1038,by decide +kernel⟩ t)
def piece1141 : AffinePiece := pieces[1039]'(by decide +kernel)
theorem intervalAccepted1141 : candidateIntervalCheck candidate1141 (623/1000) (78/125) piece1141=true := by decide +kernel
noncomputable def cell1141 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1141 accepted1141 (623/1000) (78/125) piece1141
    intervalAccepted1141 (fun t => piece_le_psi ⟨1039,by decide +kernel⟩ t)
def piece1142 : AffinePiece := pieces[1040]'(by decide +kernel)
theorem intervalAccepted1142 : candidateIntervalCheck candidate1142 (78/125) (5/8) piece1142=true := by decide +kernel
noncomputable def cell1142 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1142 accepted1142 (78/125) (5/8) piece1142
    intervalAccepted1142 (fun t => piece_le_psi ⟨1040,by decide +kernel⟩ t)
def piece1143 : AffinePiece := pieces[1041]'(by decide +kernel)
theorem intervalAccepted1143 : candidateIntervalCheck candidate1143 (5/8) (313/500) piece1143=true := by decide +kernel
noncomputable def cell1143 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1143 accepted1143 (5/8) (313/500) piece1143
    intervalAccepted1143 (fun t => piece_le_psi ⟨1041,by decide +kernel⟩ t)
def piece1144 : AffinePiece := pieces[1042]'(by decide +kernel)
theorem intervalAccepted1144 : candidateIntervalCheck candidate1144 (313/500) (627/1000) piece1144=true := by decide +kernel
noncomputable def cell1144 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1144 accepted1144 (313/500) (627/1000) piece1144
    intervalAccepted1144 (fun t => piece_le_psi ⟨1042,by decide +kernel⟩ t)
def piece1145 : AffinePiece := pieces[1043]'(by decide +kernel)
theorem intervalAccepted1145 : candidateIntervalCheck candidate1145 (627/1000) (157/250) piece1145=true := by decide +kernel
noncomputable def cell1145 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1145 accepted1145 (627/1000) (157/250) piece1145
    intervalAccepted1145 (fun t => piece_le_psi ⟨1043,by decide +kernel⟩ t)
def piece1146 : AffinePiece := pieces[1044]'(by decide +kernel)
theorem intervalAccepted1146 : candidateIntervalCheck candidate1146 (157/250) (629/1000) piece1146=true := by decide +kernel
noncomputable def cell1146 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1146 accepted1146 (157/250) (629/1000) piece1146
    intervalAccepted1146 (fun t => piece_le_psi ⟨1044,by decide +kernel⟩ t)
def piece1147 : AffinePiece := pieces[1045]'(by decide +kernel)
theorem intervalAccepted1147 : candidateIntervalCheck candidate1147 (629/1000) (63/100) piece1147=true := by decide +kernel
noncomputable def cell1147 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1147 accepted1147 (629/1000) (63/100) piece1147
    intervalAccepted1147 (fun t => piece_le_psi ⟨1045,by decide +kernel⟩ t)
def piece1148 : AffinePiece := pieces[1046]'(by decide +kernel)
theorem intervalAccepted1148 : candidateIntervalCheck candidate1148 (63/100) (631/1000) piece1148=true := by decide +kernel
noncomputable def cell1148 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1148 accepted1148 (63/100) (631/1000) piece1148
    intervalAccepted1148 (fun t => piece_le_psi ⟨1046,by decide +kernel⟩ t)
def piece1149 : AffinePiece := pieces[1047]'(by decide +kernel)
theorem intervalAccepted1149 : candidateIntervalCheck candidate1149 (631/1000) (79/125) piece1149=true := by decide +kernel
noncomputable def cell1149 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1149 accepted1149 (631/1000) (79/125) piece1149
    intervalAccepted1149 (fun t => piece_le_psi ⟨1047,by decide +kernel⟩ t)
def piece1150 : AffinePiece := pieces[1048]'(by decide +kernel)
theorem intervalAccepted1150 : candidateIntervalCheck candidate1150 (79/125) (633/1000) piece1150=true := by decide +kernel
noncomputable def cell1150 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1150 accepted1150 (79/125) (633/1000) piece1150
    intervalAccepted1150 (fun t => piece_le_psi ⟨1048,by decide +kernel⟩ t)
def piece1151 : AffinePiece := pieces[1049]'(by decide +kernel)
theorem intervalAccepted1151 : candidateIntervalCheck candidate1151 (633/1000) (317/500) piece1151=true := by decide +kernel
noncomputable def cell1151 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1151 accepted1151 (633/1000) (317/500) piece1151
    intervalAccepted1151 (fun t => piece_le_psi ⟨1049,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1136, cell1137, cell1138, cell1139, cell1140, cell1141, cell1142, cell1143, cell1144, cell1145, cell1146, cell1147, cell1148, cell1149, cell1150, cell1151]
theorem chainAccepted : spinCellChainCheck (309/500) (317/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (309/500) (317/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0071
