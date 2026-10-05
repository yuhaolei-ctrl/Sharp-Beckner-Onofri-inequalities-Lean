module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0070

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0070
open CandidateBatch0070 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1120 : AffinePiece := pieces[1018]'(by decide +kernel)
theorem intervalAccepted1120 : candidateIntervalCheck candidate1120 (301/500) (603/1000) piece1120=true := by decide +kernel
noncomputable def cell1120 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1120 accepted1120 (301/500) (603/1000) piece1120
    intervalAccepted1120 (fun t => piece_le_psi ⟨1018,by decide +kernel⟩ t)
def piece1121 : AffinePiece := pieces[1019]'(by decide +kernel)
theorem intervalAccepted1121 : candidateIntervalCheck candidate1121 (603/1000) (151/250) piece1121=true := by decide +kernel
noncomputable def cell1121 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1121 accepted1121 (603/1000) (151/250) piece1121
    intervalAccepted1121 (fun t => piece_le_psi ⟨1019,by decide +kernel⟩ t)
def piece1122 : AffinePiece := pieces[1020]'(by decide +kernel)
theorem intervalAccepted1122 : candidateIntervalCheck candidate1122 (151/250) (121/200) piece1122=true := by decide +kernel
noncomputable def cell1122 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1122 accepted1122 (151/250) (121/200) piece1122
    intervalAccepted1122 (fun t => piece_le_psi ⟨1020,by decide +kernel⟩ t)
def piece1123 : AffinePiece := pieces[1021]'(by decide +kernel)
theorem intervalAccepted1123 : candidateIntervalCheck candidate1123 (121/200) (303/500) piece1123=true := by decide +kernel
noncomputable def cell1123 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1123 accepted1123 (121/200) (303/500) piece1123
    intervalAccepted1123 (fun t => piece_le_psi ⟨1021,by decide +kernel⟩ t)
def piece1124 : AffinePiece := pieces[1022]'(by decide +kernel)
theorem intervalAccepted1124 : candidateIntervalCheck candidate1124 (303/500) (607/1000) piece1124=true := by decide +kernel
noncomputable def cell1124 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1124 accepted1124 (303/500) (607/1000) piece1124
    intervalAccepted1124 (fun t => piece_le_psi ⟨1022,by decide +kernel⟩ t)
def piece1125 : AffinePiece := pieces[1023]'(by decide +kernel)
theorem intervalAccepted1125 : candidateIntervalCheck candidate1125 (607/1000) (76/125) piece1125=true := by decide +kernel
noncomputable def cell1125 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1125 accepted1125 (607/1000) (76/125) piece1125
    intervalAccepted1125 (fun t => piece_le_psi ⟨1023,by decide +kernel⟩ t)
def piece1126 : AffinePiece := pieces[1024]'(by decide +kernel)
theorem intervalAccepted1126 : candidateIntervalCheck candidate1126 (76/125) (609/1000) piece1126=true := by decide +kernel
noncomputable def cell1126 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1126 accepted1126 (76/125) (609/1000) piece1126
    intervalAccepted1126 (fun t => piece_le_psi ⟨1024,by decide +kernel⟩ t)
def piece1127 : AffinePiece := pieces[1025]'(by decide +kernel)
theorem intervalAccepted1127 : candidateIntervalCheck candidate1127 (609/1000) (61/100) piece1127=true := by decide +kernel
noncomputable def cell1127 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1127 accepted1127 (609/1000) (61/100) piece1127
    intervalAccepted1127 (fun t => piece_le_psi ⟨1025,by decide +kernel⟩ t)
def piece1128 : AffinePiece := pieces[1026]'(by decide +kernel)
theorem intervalAccepted1128 : candidateIntervalCheck candidate1128 (61/100) (611/1000) piece1128=true := by decide +kernel
noncomputable def cell1128 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1128 accepted1128 (61/100) (611/1000) piece1128
    intervalAccepted1128 (fun t => piece_le_psi ⟨1026,by decide +kernel⟩ t)
def piece1129 : AffinePiece := pieces[1027]'(by decide +kernel)
theorem intervalAccepted1129 : candidateIntervalCheck candidate1129 (611/1000) (153/250) piece1129=true := by decide +kernel
noncomputable def cell1129 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1129 accepted1129 (611/1000) (153/250) piece1129
    intervalAccepted1129 (fun t => piece_le_psi ⟨1027,by decide +kernel⟩ t)
def piece1130 : AffinePiece := pieces[1028]'(by decide +kernel)
theorem intervalAccepted1130 : candidateIntervalCheck candidate1130 (153/250) (613/1000) piece1130=true := by decide +kernel
noncomputable def cell1130 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1130 accepted1130 (153/250) (613/1000) piece1130
    intervalAccepted1130 (fun t => piece_le_psi ⟨1028,by decide +kernel⟩ t)
def piece1131 : AffinePiece := pieces[1029]'(by decide +kernel)
theorem intervalAccepted1131 : candidateIntervalCheck candidate1131 (613/1000) (307/500) piece1131=true := by decide +kernel
noncomputable def cell1131 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1131 accepted1131 (613/1000) (307/500) piece1131
    intervalAccepted1131 (fun t => piece_le_psi ⟨1029,by decide +kernel⟩ t)
def piece1132 : AffinePiece := pieces[1030]'(by decide +kernel)
theorem intervalAccepted1132 : candidateIntervalCheck candidate1132 (307/500) (123/200) piece1132=true := by decide +kernel
noncomputable def cell1132 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1132 accepted1132 (307/500) (123/200) piece1132
    intervalAccepted1132 (fun t => piece_le_psi ⟨1030,by decide +kernel⟩ t)
def piece1133 : AffinePiece := pieces[1031]'(by decide +kernel)
theorem intervalAccepted1133 : candidateIntervalCheck candidate1133 (123/200) (77/125) piece1133=true := by decide +kernel
noncomputable def cell1133 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1133 accepted1133 (123/200) (77/125) piece1133
    intervalAccepted1133 (fun t => piece_le_psi ⟨1031,by decide +kernel⟩ t)
def piece1134 : AffinePiece := pieces[1032]'(by decide +kernel)
theorem intervalAccepted1134 : candidateIntervalCheck candidate1134 (77/125) (617/1000) piece1134=true := by decide +kernel
noncomputable def cell1134 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1134 accepted1134 (77/125) (617/1000) piece1134
    intervalAccepted1134 (fun t => piece_le_psi ⟨1032,by decide +kernel⟩ t)
def piece1135 : AffinePiece := pieces[1033]'(by decide +kernel)
theorem intervalAccepted1135 : candidateIntervalCheck candidate1135 (617/1000) (309/500) piece1135=true := by decide +kernel
noncomputable def cell1135 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1135 accepted1135 (617/1000) (309/500) piece1135
    intervalAccepted1135 (fun t => piece_le_psi ⟨1033,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1120, cell1121, cell1122, cell1123, cell1124, cell1125, cell1126, cell1127, cell1128, cell1129, cell1130, cell1131, cell1132, cell1133, cell1134, cell1135]
theorem chainAccepted : spinCellChainCheck (301/500) (309/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (301/500) (309/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0070
