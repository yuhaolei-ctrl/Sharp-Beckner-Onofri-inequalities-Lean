module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0072

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0072
open CandidateBatch0072 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1152 : AffinePiece := pieces[1050]'(by decide +kernel)
theorem intervalAccepted1152 : candidateIntervalCheck candidate1152 (317/500) (127/200) piece1152=true := by decide +kernel
noncomputable def cell1152 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1152 accepted1152 (317/500) (127/200) piece1152
    intervalAccepted1152 (fun t => piece_le_psi ⟨1050,by decide +kernel⟩ t)
def piece1153 : AffinePiece := pieces[1051]'(by decide +kernel)
theorem intervalAccepted1153 : candidateIntervalCheck candidate1153 (127/200) (159/250) piece1153=true := by decide +kernel
noncomputable def cell1153 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1153 accepted1153 (127/200) (159/250) piece1153
    intervalAccepted1153 (fun t => piece_le_psi ⟨1051,by decide +kernel⟩ t)
def piece1154 : AffinePiece := pieces[1052]'(by decide +kernel)
theorem intervalAccepted1154 : candidateIntervalCheck candidate1154 (159/250) (637/1000) piece1154=true := by decide +kernel
noncomputable def cell1154 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1154 accepted1154 (159/250) (637/1000) piece1154
    intervalAccepted1154 (fun t => piece_le_psi ⟨1052,by decide +kernel⟩ t)
def piece1155 : AffinePiece := pieces[1053]'(by decide +kernel)
theorem intervalAccepted1155 : candidateIntervalCheck candidate1155 (637/1000) (319/500) piece1155=true := by decide +kernel
noncomputable def cell1155 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1155 accepted1155 (637/1000) (319/500) piece1155
    intervalAccepted1155 (fun t => piece_le_psi ⟨1053,by decide +kernel⟩ t)
def piece1156 : AffinePiece := pieces[1054]'(by decide +kernel)
theorem intervalAccepted1156 : candidateIntervalCheck candidate1156 (319/500) (639/1000) piece1156=true := by decide +kernel
noncomputable def cell1156 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1156 accepted1156 (319/500) (639/1000) piece1156
    intervalAccepted1156 (fun t => piece_le_psi ⟨1054,by decide +kernel⟩ t)
def piece1157 : AffinePiece := pieces[1055]'(by decide +kernel)
theorem intervalAccepted1157 : candidateIntervalCheck candidate1157 (639/1000) (16/25) piece1157=true := by decide +kernel
noncomputable def cell1157 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1157 accepted1157 (639/1000) (16/25) piece1157
    intervalAccepted1157 (fun t => piece_le_psi ⟨1055,by decide +kernel⟩ t)
def piece1158 : AffinePiece := pieces[1056]'(by decide +kernel)
theorem intervalAccepted1158 : candidateIntervalCheck candidate1158 (16/25) (641/1000) piece1158=true := by decide +kernel
noncomputable def cell1158 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1158 accepted1158 (16/25) (641/1000) piece1158
    intervalAccepted1158 (fun t => piece_le_psi ⟨1056,by decide +kernel⟩ t)
def piece1159 : AffinePiece := pieces[1057]'(by decide +kernel)
theorem intervalAccepted1159 : candidateIntervalCheck candidate1159 (641/1000) (321/500) piece1159=true := by decide +kernel
noncomputable def cell1159 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1159 accepted1159 (641/1000) (321/500) piece1159
    intervalAccepted1159 (fun t => piece_le_psi ⟨1057,by decide +kernel⟩ t)
def piece1160 : AffinePiece := pieces[1058]'(by decide +kernel)
theorem intervalAccepted1160 : candidateIntervalCheck candidate1160 (321/500) (643/1000) piece1160=true := by decide +kernel
noncomputable def cell1160 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1160 accepted1160 (321/500) (643/1000) piece1160
    intervalAccepted1160 (fun t => piece_le_psi ⟨1058,by decide +kernel⟩ t)
def piece1161 : AffinePiece := pieces[1059]'(by decide +kernel)
theorem intervalAccepted1161 : candidateIntervalCheck candidate1161 (643/1000) (161/250) piece1161=true := by decide +kernel
noncomputable def cell1161 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1161 accepted1161 (643/1000) (161/250) piece1161
    intervalAccepted1161 (fun t => piece_le_psi ⟨1059,by decide +kernel⟩ t)
def piece1162 : AffinePiece := pieces[1060]'(by decide +kernel)
theorem intervalAccepted1162 : candidateIntervalCheck candidate1162 (161/250) (129/200) piece1162=true := by decide +kernel
noncomputable def cell1162 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1162 accepted1162 (161/250) (129/200) piece1162
    intervalAccepted1162 (fun t => piece_le_psi ⟨1060,by decide +kernel⟩ t)
def piece1163 : AffinePiece := pieces[1061]'(by decide +kernel)
theorem intervalAccepted1163 : candidateIntervalCheck candidate1163 (129/200) (323/500) piece1163=true := by decide +kernel
noncomputable def cell1163 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1163 accepted1163 (129/200) (323/500) piece1163
    intervalAccepted1163 (fun t => piece_le_psi ⟨1061,by decide +kernel⟩ t)
def piece1164 : AffinePiece := pieces[1062]'(by decide +kernel)
theorem intervalAccepted1164 : candidateIntervalCheck candidate1164 (323/500) (647/1000) piece1164=true := by decide +kernel
noncomputable def cell1164 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1164 accepted1164 (323/500) (647/1000) piece1164
    intervalAccepted1164 (fun t => piece_le_psi ⟨1062,by decide +kernel⟩ t)
def piece1165 : AffinePiece := pieces[1063]'(by decide +kernel)
theorem intervalAccepted1165 : candidateIntervalCheck candidate1165 (647/1000) (81/125) piece1165=true := by decide +kernel
noncomputable def cell1165 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1165 accepted1165 (647/1000) (81/125) piece1165
    intervalAccepted1165 (fun t => piece_le_psi ⟨1063,by decide +kernel⟩ t)
def piece1166 : AffinePiece := pieces[1064]'(by decide +kernel)
theorem intervalAccepted1166 : candidateIntervalCheck candidate1166 (81/125) (649/1000) piece1166=true := by decide +kernel
noncomputable def cell1166 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1166 accepted1166 (81/125) (649/1000) piece1166
    intervalAccepted1166 (fun t => piece_le_psi ⟨1064,by decide +kernel⟩ t)
def piece1167 : AffinePiece := pieces[1065]'(by decide +kernel)
theorem intervalAccepted1167 : candidateIntervalCheck candidate1167 (649/1000) (13/20) piece1167=true := by decide +kernel
noncomputable def cell1167 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1167 accepted1167 (649/1000) (13/20) piece1167
    intervalAccepted1167 (fun t => piece_le_psi ⟨1065,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1152, cell1153, cell1154, cell1155, cell1156, cell1157, cell1158, cell1159, cell1160, cell1161, cell1162, cell1163, cell1164, cell1165, cell1166, cell1167]
theorem chainAccepted : spinCellChainCheck (317/500) (13/20) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (317/500) (13/20) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0072
