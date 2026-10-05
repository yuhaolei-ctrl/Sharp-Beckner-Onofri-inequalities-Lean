module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0004

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0004
open CandidateBatch0004 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0064 : AffinePiece := pieces[24]'(by decide +kernel)
theorem intervalAccepted0064 : candidateIntervalCheck candidate0064 (693/10000) (139/2000) piece0064=true := by decide +kernel
noncomputable def cell0064 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0064 accepted0064 (693/10000) (139/2000) piece0064
    intervalAccepted0064 (fun t => piece_le_psi ⟨24,by decide +kernel⟩ t)
def piece0065 : AffinePiece := pieces[25]'(by decide +kernel)
theorem intervalAccepted0065 : candidateIntervalCheck candidate0065 (139/2000) (697/10000) piece0065=true := by decide +kernel
noncomputable def cell0065 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0065 accepted0065 (139/2000) (697/10000) piece0065
    intervalAccepted0065 (fun t => piece_le_psi ⟨25,by decide +kernel⟩ t)
def piece0066 : AffinePiece := pieces[26]'(by decide +kernel)
theorem intervalAccepted0066 : candidateIntervalCheck candidate0066 (697/10000) (699/10000) piece0066=true := by decide +kernel
noncomputable def cell0066 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0066 accepted0066 (697/10000) (699/10000) piece0066
    intervalAccepted0066 (fun t => piece_le_psi ⟨26,by decide +kernel⟩ t)
def piece0067 : AffinePiece := pieces[27]'(by decide +kernel)
theorem intervalAccepted0067 : candidateIntervalCheck candidate0067 (699/10000) (701/10000) piece0067=true := by decide +kernel
noncomputable def cell0067 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0067 accepted0067 (699/10000) (701/10000) piece0067
    intervalAccepted0067 (fun t => piece_le_psi ⟨27,by decide +kernel⟩ t)
def piece0068 : AffinePiece := pieces[28]'(by decide +kernel)
theorem intervalAccepted0068 : candidateIntervalCheck candidate0068 (701/10000) (703/10000) piece0068=true := by decide +kernel
noncomputable def cell0068 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0068 accepted0068 (701/10000) (703/10000) piece0068
    intervalAccepted0068 (fun t => piece_le_psi ⟨28,by decide +kernel⟩ t)
def piece0069 : AffinePiece := pieces[29]'(by decide +kernel)
theorem intervalAccepted0069 : candidateIntervalCheck candidate0069 (703/10000) (141/2000) piece0069=true := by decide +kernel
noncomputable def cell0069 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0069 accepted0069 (703/10000) (141/2000) piece0069
    intervalAccepted0069 (fun t => piece_le_psi ⟨29,by decide +kernel⟩ t)
def piece0070 : AffinePiece := pieces[30]'(by decide +kernel)
theorem intervalAccepted0070 : candidateIntervalCheck candidate0070 (141/2000) (707/10000) piece0070=true := by decide +kernel
noncomputable def cell0070 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0070 accepted0070 (141/2000) (707/10000) piece0070
    intervalAccepted0070 (fun t => piece_le_psi ⟨30,by decide +kernel⟩ t)
def piece0071 : AffinePiece := pieces[31]'(by decide +kernel)
theorem intervalAccepted0071 : candidateIntervalCheck candidate0071 (707/10000) (709/10000) piece0071=true := by decide +kernel
noncomputable def cell0071 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0071 accepted0071 (707/10000) (709/10000) piece0071
    intervalAccepted0071 (fun t => piece_le_psi ⟨31,by decide +kernel⟩ t)
def piece0072 : AffinePiece := pieces[32]'(by decide +kernel)
theorem intervalAccepted0072 : candidateIntervalCheck candidate0072 (709/10000) (711/10000) piece0072=true := by decide +kernel
noncomputable def cell0072 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0072 accepted0072 (709/10000) (711/10000) piece0072
    intervalAccepted0072 (fun t => piece_le_psi ⟨32,by decide +kernel⟩ t)
def piece0073 : AffinePiece := pieces[33]'(by decide +kernel)
theorem intervalAccepted0073 : candidateIntervalCheck candidate0073 (711/10000) (713/10000) piece0073=true := by decide +kernel
noncomputable def cell0073 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0073 accepted0073 (711/10000) (713/10000) piece0073
    intervalAccepted0073 (fun t => piece_le_psi ⟨33,by decide +kernel⟩ t)
def piece0074 : AffinePiece := pieces[34]'(by decide +kernel)
theorem intervalAccepted0074 : candidateIntervalCheck candidate0074 (713/10000) (143/2000) piece0074=true := by decide +kernel
noncomputable def cell0074 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0074 accepted0074 (713/10000) (143/2000) piece0074
    intervalAccepted0074 (fun t => piece_le_psi ⟨34,by decide +kernel⟩ t)
def piece0075 : AffinePiece := pieces[35]'(by decide +kernel)
theorem intervalAccepted0075 : candidateIntervalCheck candidate0075 (143/2000) (717/10000) piece0075=true := by decide +kernel
noncomputable def cell0075 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0075 accepted0075 (143/2000) (717/10000) piece0075
    intervalAccepted0075 (fun t => piece_le_psi ⟨35,by decide +kernel⟩ t)
def piece0076 : AffinePiece := pieces[36]'(by decide +kernel)
theorem intervalAccepted0076 : candidateIntervalCheck candidate0076 (717/10000) (719/10000) piece0076=true := by decide +kernel
noncomputable def cell0076 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0076 accepted0076 (717/10000) (719/10000) piece0076
    intervalAccepted0076 (fun t => piece_le_psi ⟨36,by decide +kernel⟩ t)
def piece0077 : AffinePiece := pieces[37]'(by decide +kernel)
theorem intervalAccepted0077 : candidateIntervalCheck candidate0077 (719/10000) (721/10000) piece0077=true := by decide +kernel
noncomputable def cell0077 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0077 accepted0077 (719/10000) (721/10000) piece0077
    intervalAccepted0077 (fun t => piece_le_psi ⟨37,by decide +kernel⟩ t)
def piece0078 : AffinePiece := pieces[38]'(by decide +kernel)
theorem intervalAccepted0078 : candidateIntervalCheck candidate0078 (721/10000) (723/10000) piece0078=true := by decide +kernel
noncomputable def cell0078 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0078 accepted0078 (721/10000) (723/10000) piece0078
    intervalAccepted0078 (fun t => piece_le_psi ⟨38,by decide +kernel⟩ t)
def piece0079 : AffinePiece := pieces[39]'(by decide +kernel)
theorem intervalAccepted0079 : candidateIntervalCheck candidate0079 (723/10000) (29/400) piece0079=true := by decide +kernel
noncomputable def cell0079 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0079 accepted0079 (723/10000) (29/400) piece0079
    intervalAccepted0079 (fun t => piece_le_psi ⟨39,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0064, cell0065, cell0066, cell0067, cell0068, cell0069, cell0070, cell0071, cell0072, cell0073, cell0074, cell0075, cell0076, cell0077, cell0078, cell0079]
theorem chainAccepted : spinCellChainCheck (693/10000) (29/400) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (693/10000) (29/400) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0004
