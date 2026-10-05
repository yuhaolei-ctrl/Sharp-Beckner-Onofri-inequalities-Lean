module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0009

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0009
open CandidateBatch0009 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0144 : AffinePiece := pieces[104]'(by decide +kernel)
theorem intervalAccepted0144 : candidateIntervalCheck candidate0144 (853/10000) (171/2000) piece0144=true := by decide +kernel
noncomputable def cell0144 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0144 accepted0144 (853/10000) (171/2000) piece0144
    intervalAccepted0144 (fun t => piece_le_psi ⟨104,by decide +kernel⟩ t)
def piece0145 : AffinePiece := pieces[105]'(by decide +kernel)
theorem intervalAccepted0145 : candidateIntervalCheck candidate0145 (171/2000) (857/10000) piece0145=true := by decide +kernel
noncomputable def cell0145 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0145 accepted0145 (171/2000) (857/10000) piece0145
    intervalAccepted0145 (fun t => piece_le_psi ⟨105,by decide +kernel⟩ t)
def piece0146 : AffinePiece := pieces[106]'(by decide +kernel)
theorem intervalAccepted0146 : candidateIntervalCheck candidate0146 (857/10000) (859/10000) piece0146=true := by decide +kernel
noncomputable def cell0146 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0146 accepted0146 (857/10000) (859/10000) piece0146
    intervalAccepted0146 (fun t => piece_le_psi ⟨106,by decide +kernel⟩ t)
def piece0147 : AffinePiece := pieces[107]'(by decide +kernel)
theorem intervalAccepted0147 : candidateIntervalCheck candidate0147 (859/10000) (861/10000) piece0147=true := by decide +kernel
noncomputable def cell0147 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0147 accepted0147 (859/10000) (861/10000) piece0147
    intervalAccepted0147 (fun t => piece_le_psi ⟨107,by decide +kernel⟩ t)
def piece0148 : AffinePiece := pieces[108]'(by decide +kernel)
theorem intervalAccepted0148 : candidateIntervalCheck candidate0148 (861/10000) (863/10000) piece0148=true := by decide +kernel
noncomputable def cell0148 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0148 accepted0148 (861/10000) (863/10000) piece0148
    intervalAccepted0148 (fun t => piece_le_psi ⟨108,by decide +kernel⟩ t)
def piece0149 : AffinePiece := pieces[109]'(by decide +kernel)
theorem intervalAccepted0149 : candidateIntervalCheck candidate0149 (863/10000) (173/2000) piece0149=true := by decide +kernel
noncomputable def cell0149 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0149 accepted0149 (863/10000) (173/2000) piece0149
    intervalAccepted0149 (fun t => piece_le_psi ⟨109,by decide +kernel⟩ t)
def piece0150 : AffinePiece := pieces[110]'(by decide +kernel)
theorem intervalAccepted0150 : candidateIntervalCheck candidate0150 (173/2000) (867/10000) piece0150=true := by decide +kernel
noncomputable def cell0150 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0150 accepted0150 (173/2000) (867/10000) piece0150
    intervalAccepted0150 (fun t => piece_le_psi ⟨110,by decide +kernel⟩ t)
def piece0151 : AffinePiece := pieces[111]'(by decide +kernel)
theorem intervalAccepted0151 : candidateIntervalCheck candidate0151 (867/10000) (869/10000) piece0151=true := by decide +kernel
noncomputable def cell0151 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0151 accepted0151 (867/10000) (869/10000) piece0151
    intervalAccepted0151 (fun t => piece_le_psi ⟨111,by decide +kernel⟩ t)
def piece0152 : AffinePiece := pieces[112]'(by decide +kernel)
theorem intervalAccepted0152 : candidateIntervalCheck candidate0152 (869/10000) (871/10000) piece0152=true := by decide +kernel
noncomputable def cell0152 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0152 accepted0152 (869/10000) (871/10000) piece0152
    intervalAccepted0152 (fun t => piece_le_psi ⟨112,by decide +kernel⟩ t)
def piece0153 : AffinePiece := pieces[113]'(by decide +kernel)
theorem intervalAccepted0153 : candidateIntervalCheck candidate0153 (871/10000) (873/10000) piece0153=true := by decide +kernel
noncomputable def cell0153 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0153 accepted0153 (871/10000) (873/10000) piece0153
    intervalAccepted0153 (fun t => piece_le_psi ⟨113,by decide +kernel⟩ t)
def piece0154 : AffinePiece := pieces[114]'(by decide +kernel)
theorem intervalAccepted0154 : candidateIntervalCheck candidate0154 (873/10000) (7/80) piece0154=true := by decide +kernel
noncomputable def cell0154 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0154 accepted0154 (873/10000) (7/80) piece0154
    intervalAccepted0154 (fun t => piece_le_psi ⟨114,by decide +kernel⟩ t)
def piece0155 : AffinePiece := pieces[115]'(by decide +kernel)
theorem intervalAccepted0155 : candidateIntervalCheck candidate0155 (7/80) (877/10000) piece0155=true := by decide +kernel
noncomputable def cell0155 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0155 accepted0155 (7/80) (877/10000) piece0155
    intervalAccepted0155 (fun t => piece_le_psi ⟨115,by decide +kernel⟩ t)
def piece0156 : AffinePiece := pieces[116]'(by decide +kernel)
theorem intervalAccepted0156 : candidateIntervalCheck candidate0156 (877/10000) (879/10000) piece0156=true := by decide +kernel
noncomputable def cell0156 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0156 accepted0156 (877/10000) (879/10000) piece0156
    intervalAccepted0156 (fun t => piece_le_psi ⟨116,by decide +kernel⟩ t)
def piece0157 : AffinePiece := pieces[117]'(by decide +kernel)
theorem intervalAccepted0157 : candidateIntervalCheck candidate0157 (879/10000) (881/10000) piece0157=true := by decide +kernel
noncomputable def cell0157 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0157 accepted0157 (879/10000) (881/10000) piece0157
    intervalAccepted0157 (fun t => piece_le_psi ⟨117,by decide +kernel⟩ t)
def piece0158 : AffinePiece := pieces[118]'(by decide +kernel)
theorem intervalAccepted0158 : candidateIntervalCheck candidate0158 (881/10000) (883/10000) piece0158=true := by decide +kernel
noncomputable def cell0158 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0158 accepted0158 (881/10000) (883/10000) piece0158
    intervalAccepted0158 (fun t => piece_le_psi ⟨118,by decide +kernel⟩ t)
def piece0159 : AffinePiece := pieces[119]'(by decide +kernel)
theorem intervalAccepted0159 : candidateIntervalCheck candidate0159 (883/10000) (177/2000) piece0159=true := by decide +kernel
noncomputable def cell0159 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0159 accepted0159 (883/10000) (177/2000) piece0159
    intervalAccepted0159 (fun t => piece_le_psi ⟨119,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0144, cell0145, cell0146, cell0147, cell0148, cell0149, cell0150, cell0151, cell0152, cell0153, cell0154, cell0155, cell0156, cell0157, cell0158, cell0159]
theorem chainAccepted : spinCellChainCheck (853/10000) (177/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (853/10000) (177/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0009
