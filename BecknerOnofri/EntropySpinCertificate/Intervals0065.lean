module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0065

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0065
open CandidateBatch0065 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1040 : AffinePiece := pieces[938]'(by decide +kernel)
theorem intervalAccepted1040 : candidateIntervalCheck candidate1040 (261/500) (523/1000) piece1040=true := by decide +kernel
noncomputable def cell1040 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1040 accepted1040 (261/500) (523/1000) piece1040
    intervalAccepted1040 (fun t => piece_le_psi ⟨938,by decide +kernel⟩ t)
def piece1041 : AffinePiece := pieces[939]'(by decide +kernel)
theorem intervalAccepted1041 : candidateIntervalCheck candidate1041 (523/1000) (131/250) piece1041=true := by decide +kernel
noncomputable def cell1041 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1041 accepted1041 (523/1000) (131/250) piece1041
    intervalAccepted1041 (fun t => piece_le_psi ⟨939,by decide +kernel⟩ t)
def piece1042 : AffinePiece := pieces[940]'(by decide +kernel)
theorem intervalAccepted1042 : candidateIntervalCheck candidate1042 (131/250) (21/40) piece1042=true := by decide +kernel
noncomputable def cell1042 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1042 accepted1042 (131/250) (21/40) piece1042
    intervalAccepted1042 (fun t => piece_le_psi ⟨940,by decide +kernel⟩ t)
def piece1043 : AffinePiece := pieces[941]'(by decide +kernel)
theorem intervalAccepted1043 : candidateIntervalCheck candidate1043 (21/40) (263/500) piece1043=true := by decide +kernel
noncomputable def cell1043 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1043 accepted1043 (21/40) (263/500) piece1043
    intervalAccepted1043 (fun t => piece_le_psi ⟨941,by decide +kernel⟩ t)
def piece1044 : AffinePiece := pieces[942]'(by decide +kernel)
theorem intervalAccepted1044 : candidateIntervalCheck candidate1044 (263/500) (527/1000) piece1044=true := by decide +kernel
noncomputable def cell1044 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1044 accepted1044 (263/500) (527/1000) piece1044
    intervalAccepted1044 (fun t => piece_le_psi ⟨942,by decide +kernel⟩ t)
def piece1045 : AffinePiece := pieces[943]'(by decide +kernel)
theorem intervalAccepted1045 : candidateIntervalCheck candidate1045 (527/1000) (66/125) piece1045=true := by decide +kernel
noncomputable def cell1045 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1045 accepted1045 (527/1000) (66/125) piece1045
    intervalAccepted1045 (fun t => piece_le_psi ⟨943,by decide +kernel⟩ t)
def piece1046 : AffinePiece := pieces[944]'(by decide +kernel)
theorem intervalAccepted1046 : candidateIntervalCheck candidate1046 (66/125) (529/1000) piece1046=true := by decide +kernel
noncomputable def cell1046 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1046 accepted1046 (66/125) (529/1000) piece1046
    intervalAccepted1046 (fun t => piece_le_psi ⟨944,by decide +kernel⟩ t)
def piece1047 : AffinePiece := pieces[945]'(by decide +kernel)
theorem intervalAccepted1047 : candidateIntervalCheck candidate1047 (529/1000) (53/100) piece1047=true := by decide +kernel
noncomputable def cell1047 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1047 accepted1047 (529/1000) (53/100) piece1047
    intervalAccepted1047 (fun t => piece_le_psi ⟨945,by decide +kernel⟩ t)
def piece1048 : AffinePiece := pieces[946]'(by decide +kernel)
theorem intervalAccepted1048 : candidateIntervalCheck candidate1048 (53/100) (531/1000) piece1048=true := by decide +kernel
noncomputable def cell1048 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1048 accepted1048 (53/100) (531/1000) piece1048
    intervalAccepted1048 (fun t => piece_le_psi ⟨946,by decide +kernel⟩ t)
def piece1049 : AffinePiece := pieces[947]'(by decide +kernel)
theorem intervalAccepted1049 : candidateIntervalCheck candidate1049 (531/1000) (133/250) piece1049=true := by decide +kernel
noncomputable def cell1049 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1049 accepted1049 (531/1000) (133/250) piece1049
    intervalAccepted1049 (fun t => piece_le_psi ⟨947,by decide +kernel⟩ t)
def piece1050 : AffinePiece := pieces[948]'(by decide +kernel)
theorem intervalAccepted1050 : candidateIntervalCheck candidate1050 (133/250) (533/1000) piece1050=true := by decide +kernel
noncomputable def cell1050 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1050 accepted1050 (133/250) (533/1000) piece1050
    intervalAccepted1050 (fun t => piece_le_psi ⟨948,by decide +kernel⟩ t)
def piece1051 : AffinePiece := pieces[949]'(by decide +kernel)
theorem intervalAccepted1051 : candidateIntervalCheck candidate1051 (533/1000) (267/500) piece1051=true := by decide +kernel
noncomputable def cell1051 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1051 accepted1051 (533/1000) (267/500) piece1051
    intervalAccepted1051 (fun t => piece_le_psi ⟨949,by decide +kernel⟩ t)
def piece1052 : AffinePiece := pieces[950]'(by decide +kernel)
theorem intervalAccepted1052 : candidateIntervalCheck candidate1052 (267/500) (107/200) piece1052=true := by decide +kernel
noncomputable def cell1052 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1052 accepted1052 (267/500) (107/200) piece1052
    intervalAccepted1052 (fun t => piece_le_psi ⟨950,by decide +kernel⟩ t)
def piece1053 : AffinePiece := pieces[951]'(by decide +kernel)
theorem intervalAccepted1053 : candidateIntervalCheck candidate1053 (107/200) (67/125) piece1053=true := by decide +kernel
noncomputable def cell1053 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1053 accepted1053 (107/200) (67/125) piece1053
    intervalAccepted1053 (fun t => piece_le_psi ⟨951,by decide +kernel⟩ t)
def piece1054 : AffinePiece := pieces[952]'(by decide +kernel)
theorem intervalAccepted1054 : candidateIntervalCheck candidate1054 (67/125) (537/1000) piece1054=true := by decide +kernel
noncomputable def cell1054 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1054 accepted1054 (67/125) (537/1000) piece1054
    intervalAccepted1054 (fun t => piece_le_psi ⟨952,by decide +kernel⟩ t)
def piece1055 : AffinePiece := pieces[953]'(by decide +kernel)
theorem intervalAccepted1055 : candidateIntervalCheck candidate1055 (537/1000) (269/500) piece1055=true := by decide +kernel
noncomputable def cell1055 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1055 accepted1055 (537/1000) (269/500) piece1055
    intervalAccepted1055 (fun t => piece_le_psi ⟨953,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1040, cell1041, cell1042, cell1043, cell1044, cell1045, cell1046, cell1047, cell1048, cell1049, cell1050, cell1051, cell1052, cell1053, cell1054, cell1055]
theorem chainAccepted : spinCellChainCheck (261/500) (269/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (261/500) (269/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0065
