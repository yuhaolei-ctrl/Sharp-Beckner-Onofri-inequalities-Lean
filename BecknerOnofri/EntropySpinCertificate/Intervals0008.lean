module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0008

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0008
open CandidateBatch0008 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0128 : AffinePiece := pieces[88]'(by decide +kernel)
theorem intervalAccepted0128 : candidateIntervalCheck candidate0128 (821/10000) (823/10000) piece0128=true := by decide +kernel
noncomputable def cell0128 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0128 accepted0128 (821/10000) (823/10000) piece0128
    intervalAccepted0128 (fun t => piece_le_psi ⟨88,by decide +kernel⟩ t)
def piece0129 : AffinePiece := pieces[89]'(by decide +kernel)
theorem intervalAccepted0129 : candidateIntervalCheck candidate0129 (823/10000) (33/400) piece0129=true := by decide +kernel
noncomputable def cell0129 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0129 accepted0129 (823/10000) (33/400) piece0129
    intervalAccepted0129 (fun t => piece_le_psi ⟨89,by decide +kernel⟩ t)
def piece0130 : AffinePiece := pieces[90]'(by decide +kernel)
theorem intervalAccepted0130 : candidateIntervalCheck candidate0130 (33/400) (827/10000) piece0130=true := by decide +kernel
noncomputable def cell0130 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0130 accepted0130 (33/400) (827/10000) piece0130
    intervalAccepted0130 (fun t => piece_le_psi ⟨90,by decide +kernel⟩ t)
def piece0131 : AffinePiece := pieces[91]'(by decide +kernel)
theorem intervalAccepted0131 : candidateIntervalCheck candidate0131 (827/10000) (829/10000) piece0131=true := by decide +kernel
noncomputable def cell0131 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0131 accepted0131 (827/10000) (829/10000) piece0131
    intervalAccepted0131 (fun t => piece_le_psi ⟨91,by decide +kernel⟩ t)
def piece0132 : AffinePiece := pieces[92]'(by decide +kernel)
theorem intervalAccepted0132 : candidateIntervalCheck candidate0132 (829/10000) (831/10000) piece0132=true := by decide +kernel
noncomputable def cell0132 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0132 accepted0132 (829/10000) (831/10000) piece0132
    intervalAccepted0132 (fun t => piece_le_psi ⟨92,by decide +kernel⟩ t)
def piece0133 : AffinePiece := pieces[93]'(by decide +kernel)
theorem intervalAccepted0133 : candidateIntervalCheck candidate0133 (831/10000) (833/10000) piece0133=true := by decide +kernel
noncomputable def cell0133 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0133 accepted0133 (831/10000) (833/10000) piece0133
    intervalAccepted0133 (fun t => piece_le_psi ⟨93,by decide +kernel⟩ t)
def piece0134 : AffinePiece := pieces[94]'(by decide +kernel)
theorem intervalAccepted0134 : candidateIntervalCheck candidate0134 (833/10000) (167/2000) piece0134=true := by decide +kernel
noncomputable def cell0134 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0134 accepted0134 (833/10000) (167/2000) piece0134
    intervalAccepted0134 (fun t => piece_le_psi ⟨94,by decide +kernel⟩ t)
def piece0135 : AffinePiece := pieces[95]'(by decide +kernel)
theorem intervalAccepted0135 : candidateIntervalCheck candidate0135 (167/2000) (837/10000) piece0135=true := by decide +kernel
noncomputable def cell0135 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0135 accepted0135 (167/2000) (837/10000) piece0135
    intervalAccepted0135 (fun t => piece_le_psi ⟨95,by decide +kernel⟩ t)
def piece0136 : AffinePiece := pieces[96]'(by decide +kernel)
theorem intervalAccepted0136 : candidateIntervalCheck candidate0136 (837/10000) (839/10000) piece0136=true := by decide +kernel
noncomputable def cell0136 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0136 accepted0136 (837/10000) (839/10000) piece0136
    intervalAccepted0136 (fun t => piece_le_psi ⟨96,by decide +kernel⟩ t)
def piece0137 : AffinePiece := pieces[97]'(by decide +kernel)
theorem intervalAccepted0137 : candidateIntervalCheck candidate0137 (839/10000) (841/10000) piece0137=true := by decide +kernel
noncomputable def cell0137 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0137 accepted0137 (839/10000) (841/10000) piece0137
    intervalAccepted0137 (fun t => piece_le_psi ⟨97,by decide +kernel⟩ t)
def piece0138 : AffinePiece := pieces[98]'(by decide +kernel)
theorem intervalAccepted0138 : candidateIntervalCheck candidate0138 (841/10000) (843/10000) piece0138=true := by decide +kernel
noncomputable def cell0138 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0138 accepted0138 (841/10000) (843/10000) piece0138
    intervalAccepted0138 (fun t => piece_le_psi ⟨98,by decide +kernel⟩ t)
def piece0139 : AffinePiece := pieces[99]'(by decide +kernel)
theorem intervalAccepted0139 : candidateIntervalCheck candidate0139 (843/10000) (169/2000) piece0139=true := by decide +kernel
noncomputable def cell0139 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0139 accepted0139 (843/10000) (169/2000) piece0139
    intervalAccepted0139 (fun t => piece_le_psi ⟨99,by decide +kernel⟩ t)
def piece0140 : AffinePiece := pieces[100]'(by decide +kernel)
theorem intervalAccepted0140 : candidateIntervalCheck candidate0140 (169/2000) (847/10000) piece0140=true := by decide +kernel
noncomputable def cell0140 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0140 accepted0140 (169/2000) (847/10000) piece0140
    intervalAccepted0140 (fun t => piece_le_psi ⟨100,by decide +kernel⟩ t)
def piece0141 : AffinePiece := pieces[101]'(by decide +kernel)
theorem intervalAccepted0141 : candidateIntervalCheck candidate0141 (847/10000) (849/10000) piece0141=true := by decide +kernel
noncomputable def cell0141 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0141 accepted0141 (847/10000) (849/10000) piece0141
    intervalAccepted0141 (fun t => piece_le_psi ⟨101,by decide +kernel⟩ t)
def piece0142 : AffinePiece := pieces[102]'(by decide +kernel)
theorem intervalAccepted0142 : candidateIntervalCheck candidate0142 (849/10000) (851/10000) piece0142=true := by decide +kernel
noncomputable def cell0142 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0142 accepted0142 (849/10000) (851/10000) piece0142
    intervalAccepted0142 (fun t => piece_le_psi ⟨102,by decide +kernel⟩ t)
def piece0143 : AffinePiece := pieces[103]'(by decide +kernel)
theorem intervalAccepted0143 : candidateIntervalCheck candidate0143 (851/10000) (853/10000) piece0143=true := by decide +kernel
noncomputable def cell0143 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0143 accepted0143 (851/10000) (853/10000) piece0143
    intervalAccepted0143 (fun t => piece_le_psi ⟨103,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0128, cell0129, cell0130, cell0131, cell0132, cell0133, cell0134, cell0135, cell0136, cell0137, cell0138, cell0139, cell0140, cell0141, cell0142, cell0143]
theorem chainAccepted : spinCellChainCheck (821/10000) (853/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (821/10000) (853/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0008
