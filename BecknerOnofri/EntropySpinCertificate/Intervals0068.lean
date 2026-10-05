module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0068

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0068
open CandidateBatch0068 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1088 : AffinePiece := pieces[986]'(by decide +kernel)
theorem intervalAccepted1088 : candidateIntervalCheck candidate1088 (57/100) (571/1000) piece1088=true := by decide +kernel
noncomputable def cell1088 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1088 accepted1088 (57/100) (571/1000) piece1088
    intervalAccepted1088 (fun t => piece_le_psi ⟨986,by decide +kernel⟩ t)
def piece1089 : AffinePiece := pieces[987]'(by decide +kernel)
theorem intervalAccepted1089 : candidateIntervalCheck candidate1089 (571/1000) (143/250) piece1089=true := by decide +kernel
noncomputable def cell1089 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1089 accepted1089 (571/1000) (143/250) piece1089
    intervalAccepted1089 (fun t => piece_le_psi ⟨987,by decide +kernel⟩ t)
def piece1090 : AffinePiece := pieces[988]'(by decide +kernel)
theorem intervalAccepted1090 : candidateIntervalCheck candidate1090 (143/250) (573/1000) piece1090=true := by decide +kernel
noncomputable def cell1090 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1090 accepted1090 (143/250) (573/1000) piece1090
    intervalAccepted1090 (fun t => piece_le_psi ⟨988,by decide +kernel⟩ t)
def piece1091 : AffinePiece := pieces[989]'(by decide +kernel)
theorem intervalAccepted1091 : candidateIntervalCheck candidate1091 (573/1000) (287/500) piece1091=true := by decide +kernel
noncomputable def cell1091 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1091 accepted1091 (573/1000) (287/500) piece1091
    intervalAccepted1091 (fun t => piece_le_psi ⟨989,by decide +kernel⟩ t)
def piece1092 : AffinePiece := pieces[990]'(by decide +kernel)
theorem intervalAccepted1092 : candidateIntervalCheck candidate1092 (287/500) (23/40) piece1092=true := by decide +kernel
noncomputable def cell1092 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1092 accepted1092 (287/500) (23/40) piece1092
    intervalAccepted1092 (fun t => piece_le_psi ⟨990,by decide +kernel⟩ t)
def piece1093 : AffinePiece := pieces[991]'(by decide +kernel)
theorem intervalAccepted1093 : candidateIntervalCheck candidate1093 (23/40) (72/125) piece1093=true := by decide +kernel
noncomputable def cell1093 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1093 accepted1093 (23/40) (72/125) piece1093
    intervalAccepted1093 (fun t => piece_le_psi ⟨991,by decide +kernel⟩ t)
def piece1094 : AffinePiece := pieces[992]'(by decide +kernel)
theorem intervalAccepted1094 : candidateIntervalCheck candidate1094 (72/125) (577/1000) piece1094=true := by decide +kernel
noncomputable def cell1094 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1094 accepted1094 (72/125) (577/1000) piece1094
    intervalAccepted1094 (fun t => piece_le_psi ⟨992,by decide +kernel⟩ t)
def piece1095 : AffinePiece := pieces[993]'(by decide +kernel)
theorem intervalAccepted1095 : candidateIntervalCheck candidate1095 (577/1000) (289/500) piece1095=true := by decide +kernel
noncomputable def cell1095 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1095 accepted1095 (577/1000) (289/500) piece1095
    intervalAccepted1095 (fun t => piece_le_psi ⟨993,by decide +kernel⟩ t)
def piece1096 : AffinePiece := pieces[994]'(by decide +kernel)
theorem intervalAccepted1096 : candidateIntervalCheck candidate1096 (289/500) (579/1000) piece1096=true := by decide +kernel
noncomputable def cell1096 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1096 accepted1096 (289/500) (579/1000) piece1096
    intervalAccepted1096 (fun t => piece_le_psi ⟨994,by decide +kernel⟩ t)
def piece1097 : AffinePiece := pieces[995]'(by decide +kernel)
theorem intervalAccepted1097 : candidateIntervalCheck candidate1097 (579/1000) (29/50) piece1097=true := by decide +kernel
noncomputable def cell1097 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1097 accepted1097 (579/1000) (29/50) piece1097
    intervalAccepted1097 (fun t => piece_le_psi ⟨995,by decide +kernel⟩ t)
def piece1098 : AffinePiece := pieces[996]'(by decide +kernel)
theorem intervalAccepted1098 : candidateIntervalCheck candidate1098 (29/50) (581/1000) piece1098=true := by decide +kernel
noncomputable def cell1098 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1098 accepted1098 (29/50) (581/1000) piece1098
    intervalAccepted1098 (fun t => piece_le_psi ⟨996,by decide +kernel⟩ t)
def piece1099 : AffinePiece := pieces[997]'(by decide +kernel)
theorem intervalAccepted1099 : candidateIntervalCheck candidate1099 (581/1000) (291/500) piece1099=true := by decide +kernel
noncomputable def cell1099 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1099 accepted1099 (581/1000) (291/500) piece1099
    intervalAccepted1099 (fun t => piece_le_psi ⟨997,by decide +kernel⟩ t)
def piece1100 : AffinePiece := pieces[998]'(by decide +kernel)
theorem intervalAccepted1100 : candidateIntervalCheck candidate1100 (291/500) (583/1000) piece1100=true := by decide +kernel
noncomputable def cell1100 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1100 accepted1100 (291/500) (583/1000) piece1100
    intervalAccepted1100 (fun t => piece_le_psi ⟨998,by decide +kernel⟩ t)
def piece1101 : AffinePiece := pieces[999]'(by decide +kernel)
theorem intervalAccepted1101 : candidateIntervalCheck candidate1101 (583/1000) (73/125) piece1101=true := by decide +kernel
noncomputable def cell1101 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1101 accepted1101 (583/1000) (73/125) piece1101
    intervalAccepted1101 (fun t => piece_le_psi ⟨999,by decide +kernel⟩ t)
def piece1102 : AffinePiece := pieces[1000]'(by decide +kernel)
theorem intervalAccepted1102 : candidateIntervalCheck candidate1102 (73/125) (117/200) piece1102=true := by decide +kernel
noncomputable def cell1102 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1102 accepted1102 (73/125) (117/200) piece1102
    intervalAccepted1102 (fun t => piece_le_psi ⟨1000,by decide +kernel⟩ t)
def piece1103 : AffinePiece := pieces[1001]'(by decide +kernel)
theorem intervalAccepted1103 : candidateIntervalCheck candidate1103 (117/200) (293/500) piece1103=true := by decide +kernel
noncomputable def cell1103 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1103 accepted1103 (117/200) (293/500) piece1103
    intervalAccepted1103 (fun t => piece_le_psi ⟨1001,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1088, cell1089, cell1090, cell1091, cell1092, cell1093, cell1094, cell1095, cell1096, cell1097, cell1098, cell1099, cell1100, cell1101, cell1102, cell1103]
theorem chainAccepted : spinCellChainCheck (57/100) (293/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (57/100) (293/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0068
