module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0005

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0005
open CandidateBatch0005 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0080 : AffinePiece := pieces[40]'(by decide +kernel)
theorem intervalAccepted0080 : candidateIntervalCheck candidate0080 (29/400) (727/10000) piece0080=true := by decide +kernel
noncomputable def cell0080 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0080 accepted0080 (29/400) (727/10000) piece0080
    intervalAccepted0080 (fun t => piece_le_psi ⟨40,by decide +kernel⟩ t)
def piece0081 : AffinePiece := pieces[41]'(by decide +kernel)
theorem intervalAccepted0081 : candidateIntervalCheck candidate0081 (727/10000) (729/10000) piece0081=true := by decide +kernel
noncomputable def cell0081 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0081 accepted0081 (727/10000) (729/10000) piece0081
    intervalAccepted0081 (fun t => piece_le_psi ⟨41,by decide +kernel⟩ t)
def piece0082 : AffinePiece := pieces[42]'(by decide +kernel)
theorem intervalAccepted0082 : candidateIntervalCheck candidate0082 (729/10000) (731/10000) piece0082=true := by decide +kernel
noncomputable def cell0082 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0082 accepted0082 (729/10000) (731/10000) piece0082
    intervalAccepted0082 (fun t => piece_le_psi ⟨42,by decide +kernel⟩ t)
def piece0083 : AffinePiece := pieces[43]'(by decide +kernel)
theorem intervalAccepted0083 : candidateIntervalCheck candidate0083 (731/10000) (733/10000) piece0083=true := by decide +kernel
noncomputable def cell0083 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0083 accepted0083 (731/10000) (733/10000) piece0083
    intervalAccepted0083 (fun t => piece_le_psi ⟨43,by decide +kernel⟩ t)
def piece0084 : AffinePiece := pieces[44]'(by decide +kernel)
theorem intervalAccepted0084 : candidateIntervalCheck candidate0084 (733/10000) (147/2000) piece0084=true := by decide +kernel
noncomputable def cell0084 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0084 accepted0084 (733/10000) (147/2000) piece0084
    intervalAccepted0084 (fun t => piece_le_psi ⟨44,by decide +kernel⟩ t)
def piece0085 : AffinePiece := pieces[45]'(by decide +kernel)
theorem intervalAccepted0085 : candidateIntervalCheck candidate0085 (147/2000) (737/10000) piece0085=true := by decide +kernel
noncomputable def cell0085 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0085 accepted0085 (147/2000) (737/10000) piece0085
    intervalAccepted0085 (fun t => piece_le_psi ⟨45,by decide +kernel⟩ t)
def piece0086 : AffinePiece := pieces[46]'(by decide +kernel)
theorem intervalAccepted0086 : candidateIntervalCheck candidate0086 (737/10000) (739/10000) piece0086=true := by decide +kernel
noncomputable def cell0086 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0086 accepted0086 (737/10000) (739/10000) piece0086
    intervalAccepted0086 (fun t => piece_le_psi ⟨46,by decide +kernel⟩ t)
def piece0087 : AffinePiece := pieces[47]'(by decide +kernel)
theorem intervalAccepted0087 : candidateIntervalCheck candidate0087 (739/10000) (741/10000) piece0087=true := by decide +kernel
noncomputable def cell0087 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0087 accepted0087 (739/10000) (741/10000) piece0087
    intervalAccepted0087 (fun t => piece_le_psi ⟨47,by decide +kernel⟩ t)
def piece0088 : AffinePiece := pieces[48]'(by decide +kernel)
theorem intervalAccepted0088 : candidateIntervalCheck candidate0088 (741/10000) (743/10000) piece0088=true := by decide +kernel
noncomputable def cell0088 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0088 accepted0088 (741/10000) (743/10000) piece0088
    intervalAccepted0088 (fun t => piece_le_psi ⟨48,by decide +kernel⟩ t)
def piece0089 : AffinePiece := pieces[49]'(by decide +kernel)
theorem intervalAccepted0089 : candidateIntervalCheck candidate0089 (743/10000) (149/2000) piece0089=true := by decide +kernel
noncomputable def cell0089 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0089 accepted0089 (743/10000) (149/2000) piece0089
    intervalAccepted0089 (fun t => piece_le_psi ⟨49,by decide +kernel⟩ t)
def piece0090 : AffinePiece := pieces[50]'(by decide +kernel)
theorem intervalAccepted0090 : candidateIntervalCheck candidate0090 (149/2000) (747/10000) piece0090=true := by decide +kernel
noncomputable def cell0090 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0090 accepted0090 (149/2000) (747/10000) piece0090
    intervalAccepted0090 (fun t => piece_le_psi ⟨50,by decide +kernel⟩ t)
def piece0091 : AffinePiece := pieces[51]'(by decide +kernel)
theorem intervalAccepted0091 : candidateIntervalCheck candidate0091 (747/10000) (749/10000) piece0091=true := by decide +kernel
noncomputable def cell0091 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0091 accepted0091 (747/10000) (749/10000) piece0091
    intervalAccepted0091 (fun t => piece_le_psi ⟨51,by decide +kernel⟩ t)
def piece0092 : AffinePiece := pieces[52]'(by decide +kernel)
theorem intervalAccepted0092 : candidateIntervalCheck candidate0092 (749/10000) (751/10000) piece0092=true := by decide +kernel
noncomputable def cell0092 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0092 accepted0092 (749/10000) (751/10000) piece0092
    intervalAccepted0092 (fun t => piece_le_psi ⟨52,by decide +kernel⟩ t)
def piece0093 : AffinePiece := pieces[53]'(by decide +kernel)
theorem intervalAccepted0093 : candidateIntervalCheck candidate0093 (751/10000) (753/10000) piece0093=true := by decide +kernel
noncomputable def cell0093 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0093 accepted0093 (751/10000) (753/10000) piece0093
    intervalAccepted0093 (fun t => piece_le_psi ⟨53,by decide +kernel⟩ t)
def piece0094 : AffinePiece := pieces[54]'(by decide +kernel)
theorem intervalAccepted0094 : candidateIntervalCheck candidate0094 (753/10000) (151/2000) piece0094=true := by decide +kernel
noncomputable def cell0094 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0094 accepted0094 (753/10000) (151/2000) piece0094
    intervalAccepted0094 (fun t => piece_le_psi ⟨54,by decide +kernel⟩ t)
def piece0095 : AffinePiece := pieces[55]'(by decide +kernel)
theorem intervalAccepted0095 : candidateIntervalCheck candidate0095 (151/2000) (757/10000) piece0095=true := by decide +kernel
noncomputable def cell0095 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0095 accepted0095 (151/2000) (757/10000) piece0095
    intervalAccepted0095 (fun t => piece_le_psi ⟨55,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0080, cell0081, cell0082, cell0083, cell0084, cell0085, cell0086, cell0087, cell0088, cell0089, cell0090, cell0091, cell0092, cell0093, cell0094, cell0095]
theorem chainAccepted : spinCellChainCheck (29/400) (757/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (29/400) (757/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0005
