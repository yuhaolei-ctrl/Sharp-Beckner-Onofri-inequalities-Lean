module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0069

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0069
open CandidateBatch0069 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1104 : AffinePiece := pieces[1002]'(by decide +kernel)
theorem intervalAccepted1104 : candidateIntervalCheck candidate1104 (293/500) (587/1000) piece1104=true := by decide +kernel
noncomputable def cell1104 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1104 accepted1104 (293/500) (587/1000) piece1104
    intervalAccepted1104 (fun t => piece_le_psi ⟨1002,by decide +kernel⟩ t)
def piece1105 : AffinePiece := pieces[1003]'(by decide +kernel)
theorem intervalAccepted1105 : candidateIntervalCheck candidate1105 (587/1000) (147/250) piece1105=true := by decide +kernel
noncomputable def cell1105 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1105 accepted1105 (587/1000) (147/250) piece1105
    intervalAccepted1105 (fun t => piece_le_psi ⟨1003,by decide +kernel⟩ t)
def piece1106 : AffinePiece := pieces[1004]'(by decide +kernel)
theorem intervalAccepted1106 : candidateIntervalCheck candidate1106 (147/250) (589/1000) piece1106=true := by decide +kernel
noncomputable def cell1106 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1106 accepted1106 (147/250) (589/1000) piece1106
    intervalAccepted1106 (fun t => piece_le_psi ⟨1004,by decide +kernel⟩ t)
def piece1107 : AffinePiece := pieces[1005]'(by decide +kernel)
theorem intervalAccepted1107 : candidateIntervalCheck candidate1107 (589/1000) (59/100) piece1107=true := by decide +kernel
noncomputable def cell1107 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1107 accepted1107 (589/1000) (59/100) piece1107
    intervalAccepted1107 (fun t => piece_le_psi ⟨1005,by decide +kernel⟩ t)
def piece1108 : AffinePiece := pieces[1006]'(by decide +kernel)
theorem intervalAccepted1108 : candidateIntervalCheck candidate1108 (59/100) (591/1000) piece1108=true := by decide +kernel
noncomputable def cell1108 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1108 accepted1108 (59/100) (591/1000) piece1108
    intervalAccepted1108 (fun t => piece_le_psi ⟨1006,by decide +kernel⟩ t)
def piece1109 : AffinePiece := pieces[1007]'(by decide +kernel)
theorem intervalAccepted1109 : candidateIntervalCheck candidate1109 (591/1000) (74/125) piece1109=true := by decide +kernel
noncomputable def cell1109 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1109 accepted1109 (591/1000) (74/125) piece1109
    intervalAccepted1109 (fun t => piece_le_psi ⟨1007,by decide +kernel⟩ t)
def piece1110 : AffinePiece := pieces[1008]'(by decide +kernel)
theorem intervalAccepted1110 : candidateIntervalCheck candidate1110 (74/125) (593/1000) piece1110=true := by decide +kernel
noncomputable def cell1110 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1110 accepted1110 (74/125) (593/1000) piece1110
    intervalAccepted1110 (fun t => piece_le_psi ⟨1008,by decide +kernel⟩ t)
def piece1111 : AffinePiece := pieces[1009]'(by decide +kernel)
theorem intervalAccepted1111 : candidateIntervalCheck candidate1111 (593/1000) (297/500) piece1111=true := by decide +kernel
noncomputable def cell1111 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1111 accepted1111 (593/1000) (297/500) piece1111
    intervalAccepted1111 (fun t => piece_le_psi ⟨1009,by decide +kernel⟩ t)
def piece1112 : AffinePiece := pieces[1010]'(by decide +kernel)
theorem intervalAccepted1112 : candidateIntervalCheck candidate1112 (297/500) (119/200) piece1112=true := by decide +kernel
noncomputable def cell1112 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1112 accepted1112 (297/500) (119/200) piece1112
    intervalAccepted1112 (fun t => piece_le_psi ⟨1010,by decide +kernel⟩ t)
def piece1113 : AffinePiece := pieces[1011]'(by decide +kernel)
theorem intervalAccepted1113 : candidateIntervalCheck candidate1113 (119/200) (149/250) piece1113=true := by decide +kernel
noncomputable def cell1113 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1113 accepted1113 (119/200) (149/250) piece1113
    intervalAccepted1113 (fun t => piece_le_psi ⟨1011,by decide +kernel⟩ t)
def piece1114 : AffinePiece := pieces[1012]'(by decide +kernel)
theorem intervalAccepted1114 : candidateIntervalCheck candidate1114 (149/250) (597/1000) piece1114=true := by decide +kernel
noncomputable def cell1114 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1114 accepted1114 (149/250) (597/1000) piece1114
    intervalAccepted1114 (fun t => piece_le_psi ⟨1012,by decide +kernel⟩ t)
def piece1115 : AffinePiece := pieces[1013]'(by decide +kernel)
theorem intervalAccepted1115 : candidateIntervalCheck candidate1115 (597/1000) (299/500) piece1115=true := by decide +kernel
noncomputable def cell1115 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1115 accepted1115 (597/1000) (299/500) piece1115
    intervalAccepted1115 (fun t => piece_le_psi ⟨1013,by decide +kernel⟩ t)
def piece1116 : AffinePiece := pieces[1014]'(by decide +kernel)
theorem intervalAccepted1116 : candidateIntervalCheck candidate1116 (299/500) (599/1000) piece1116=true := by decide +kernel
noncomputable def cell1116 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1116 accepted1116 (299/500) (599/1000) piece1116
    intervalAccepted1116 (fun t => piece_le_psi ⟨1014,by decide +kernel⟩ t)
def piece1117 : AffinePiece := pieces[1015]'(by decide +kernel)
theorem intervalAccepted1117 : candidateIntervalCheck candidate1117 (599/1000) (3/5) piece1117=true := by decide +kernel
noncomputable def cell1117 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1117 accepted1117 (599/1000) (3/5) piece1117
    intervalAccepted1117 (fun t => piece_le_psi ⟨1015,by decide +kernel⟩ t)
def piece1118 : AffinePiece := pieces[1016]'(by decide +kernel)
theorem intervalAccepted1118 : candidateIntervalCheck candidate1118 (3/5) (601/1000) piece1118=true := by decide +kernel
noncomputable def cell1118 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1118 accepted1118 (3/5) (601/1000) piece1118
    intervalAccepted1118 (fun t => piece_le_psi ⟨1016,by decide +kernel⟩ t)
def piece1119 : AffinePiece := pieces[1017]'(by decide +kernel)
theorem intervalAccepted1119 : candidateIntervalCheck candidate1119 (601/1000) (301/500) piece1119=true := by decide +kernel
noncomputable def cell1119 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1119 accepted1119 (601/1000) (301/500) piece1119
    intervalAccepted1119 (fun t => piece_le_psi ⟨1017,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1104, cell1105, cell1106, cell1107, cell1108, cell1109, cell1110, cell1111, cell1112, cell1113, cell1114, cell1115, cell1116, cell1117, cell1118, cell1119]
theorem chainAccepted : spinCellChainCheck (293/500) (301/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (293/500) (301/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0069
