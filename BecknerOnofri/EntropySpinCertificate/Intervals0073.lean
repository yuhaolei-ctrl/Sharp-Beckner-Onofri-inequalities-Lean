module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0073

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0073
open CandidateBatch0073 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1168 : AffinePiece := pieces[1066]'(by decide +kernel)
theorem intervalAccepted1168 : candidateIntervalCheck candidate1168 (13/20) (651/1000) piece1168=true := by decide +kernel
noncomputable def cell1168 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1168 accepted1168 (13/20) (651/1000) piece1168
    intervalAccepted1168 (fun t => piece_le_psi ⟨1066,by decide +kernel⟩ t)
def piece1169 : AffinePiece := pieces[1067]'(by decide +kernel)
theorem intervalAccepted1169 : candidateIntervalCheck candidate1169 (651/1000) (163/250) piece1169=true := by decide +kernel
noncomputable def cell1169 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1169 accepted1169 (651/1000) (163/250) piece1169
    intervalAccepted1169 (fun t => piece_le_psi ⟨1067,by decide +kernel⟩ t)
def piece1170 : AffinePiece := pieces[1068]'(by decide +kernel)
theorem intervalAccepted1170 : candidateIntervalCheck candidate1170 (163/250) (653/1000) piece1170=true := by decide +kernel
noncomputable def cell1170 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1170 accepted1170 (163/250) (653/1000) piece1170
    intervalAccepted1170 (fun t => piece_le_psi ⟨1068,by decide +kernel⟩ t)
def piece1171 : AffinePiece := pieces[1069]'(by decide +kernel)
theorem intervalAccepted1171 : candidateIntervalCheck candidate1171 (653/1000) (327/500) piece1171=true := by decide +kernel
noncomputable def cell1171 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1171 accepted1171 (653/1000) (327/500) piece1171
    intervalAccepted1171 (fun t => piece_le_psi ⟨1069,by decide +kernel⟩ t)
def piece1172 : AffinePiece := pieces[1070]'(by decide +kernel)
theorem intervalAccepted1172 : candidateIntervalCheck candidate1172 (327/500) (131/200) piece1172=true := by decide +kernel
noncomputable def cell1172 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1172 accepted1172 (327/500) (131/200) piece1172
    intervalAccepted1172 (fun t => piece_le_psi ⟨1070,by decide +kernel⟩ t)
def piece1173 : AffinePiece := pieces[1071]'(by decide +kernel)
theorem intervalAccepted1173 : candidateIntervalCheck candidate1173 (131/200) (82/125) piece1173=true := by decide +kernel
noncomputable def cell1173 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1173 accepted1173 (131/200) (82/125) piece1173
    intervalAccepted1173 (fun t => piece_le_psi ⟨1071,by decide +kernel⟩ t)
def piece1174 : AffinePiece := pieces[1072]'(by decide +kernel)
theorem intervalAccepted1174 : candidateIntervalCheck candidate1174 (82/125) (657/1000) piece1174=true := by decide +kernel
noncomputable def cell1174 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1174 accepted1174 (82/125) (657/1000) piece1174
    intervalAccepted1174 (fun t => piece_le_psi ⟨1072,by decide +kernel⟩ t)
def piece1175 : AffinePiece := pieces[1073]'(by decide +kernel)
theorem intervalAccepted1175 : candidateIntervalCheck candidate1175 (657/1000) (329/500) piece1175=true := by decide +kernel
noncomputable def cell1175 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1175 accepted1175 (657/1000) (329/500) piece1175
    intervalAccepted1175 (fun t => piece_le_psi ⟨1073,by decide +kernel⟩ t)
def piece1176 : AffinePiece := pieces[1074]'(by decide +kernel)
theorem intervalAccepted1176 : candidateIntervalCheck candidate1176 (329/500) (659/1000) piece1176=true := by decide +kernel
noncomputable def cell1176 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1176 accepted1176 (329/500) (659/1000) piece1176
    intervalAccepted1176 (fun t => piece_le_psi ⟨1074,by decide +kernel⟩ t)
def piece1177 : AffinePiece := pieces[1075]'(by decide +kernel)
theorem intervalAccepted1177 : candidateIntervalCheck candidate1177 (659/1000) (33/50) piece1177=true := by decide +kernel
noncomputable def cell1177 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1177 accepted1177 (659/1000) (33/50) piece1177
    intervalAccepted1177 (fun t => piece_le_psi ⟨1075,by decide +kernel⟩ t)
def piece1178 : AffinePiece := pieces[1076]'(by decide +kernel)
theorem intervalAccepted1178 : candidateIntervalCheck candidate1178 (33/50) (661/1000) piece1178=true := by decide +kernel
noncomputable def cell1178 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1178 accepted1178 (33/50) (661/1000) piece1178
    intervalAccepted1178 (fun t => piece_le_psi ⟨1076,by decide +kernel⟩ t)
def piece1179 : AffinePiece := pieces[1077]'(by decide +kernel)
theorem intervalAccepted1179 : candidateIntervalCheck candidate1179 (661/1000) (331/500) piece1179=true := by decide +kernel
noncomputable def cell1179 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1179 accepted1179 (661/1000) (331/500) piece1179
    intervalAccepted1179 (fun t => piece_le_psi ⟨1077,by decide +kernel⟩ t)
def piece1180 : AffinePiece := pieces[1078]'(by decide +kernel)
theorem intervalAccepted1180 : candidateIntervalCheck candidate1180 (331/500) (663/1000) piece1180=true := by decide +kernel
noncomputable def cell1180 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1180 accepted1180 (331/500) (663/1000) piece1180
    intervalAccepted1180 (fun t => piece_le_psi ⟨1078,by decide +kernel⟩ t)
def piece1181 : AffinePiece := pieces[1079]'(by decide +kernel)
theorem intervalAccepted1181 : candidateIntervalCheck candidate1181 (663/1000) (83/125) piece1181=true := by decide +kernel
noncomputable def cell1181 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1181 accepted1181 (663/1000) (83/125) piece1181
    intervalAccepted1181 (fun t => piece_le_psi ⟨1079,by decide +kernel⟩ t)
def piece1182 : AffinePiece := pieces[1080]'(by decide +kernel)
theorem intervalAccepted1182 : candidateIntervalCheck candidate1182 (83/125) (133/200) piece1182=true := by decide +kernel
noncomputable def cell1182 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1182 accepted1182 (83/125) (133/200) piece1182
    intervalAccepted1182 (fun t => piece_le_psi ⟨1080,by decide +kernel⟩ t)
def piece1183 : AffinePiece := pieces[1081]'(by decide +kernel)
theorem intervalAccepted1183 : candidateIntervalCheck candidate1183 (133/200) (333/500) piece1183=true := by decide +kernel
noncomputable def cell1183 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1183 accepted1183 (133/200) (333/500) piece1183
    intervalAccepted1183 (fun t => piece_le_psi ⟨1081,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1168, cell1169, cell1170, cell1171, cell1172, cell1173, cell1174, cell1175, cell1176, cell1177, cell1178, cell1179, cell1180, cell1181, cell1182, cell1183]
theorem chainAccepted : spinCellChainCheck (13/20) (333/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (13/20) (333/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0073
