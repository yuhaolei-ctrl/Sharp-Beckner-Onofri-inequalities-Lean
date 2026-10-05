import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0011
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0011
open CandidateBatch0011 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0176 : AffinePiece := pieces[136]'(by decide +kernel)
theorem intervalAccepted0176 : candidateIntervalCheck candidate0176 (917/10000) (919/10000) piece0176=true := by decide +kernel
noncomputable def cell0176 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0176 accepted0176 (917/10000) (919/10000) piece0176
    intervalAccepted0176 (fun t => piece_le_psi ⟨136,by decide +kernel⟩ t)
def piece0177 : AffinePiece := pieces[137]'(by decide +kernel)
theorem intervalAccepted0177 : candidateIntervalCheck candidate0177 (919/10000) (921/10000) piece0177=true := by decide +kernel
noncomputable def cell0177 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0177 accepted0177 (919/10000) (921/10000) piece0177
    intervalAccepted0177 (fun t => piece_le_psi ⟨137,by decide +kernel⟩ t)
def piece0178 : AffinePiece := pieces[138]'(by decide +kernel)
theorem intervalAccepted0178 : candidateIntervalCheck candidate0178 (921/10000) (923/10000) piece0178=true := by decide +kernel
noncomputable def cell0178 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0178 accepted0178 (921/10000) (923/10000) piece0178
    intervalAccepted0178 (fun t => piece_le_psi ⟨138,by decide +kernel⟩ t)
def piece0179 : AffinePiece := pieces[139]'(by decide +kernel)
theorem intervalAccepted0179 : candidateIntervalCheck candidate0179 (923/10000) (37/400) piece0179=true := by decide +kernel
noncomputable def cell0179 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0179 accepted0179 (923/10000) (37/400) piece0179
    intervalAccepted0179 (fun t => piece_le_psi ⟨139,by decide +kernel⟩ t)
def piece0180 : AffinePiece := pieces[140]'(by decide +kernel)
theorem intervalAccepted0180 : candidateIntervalCheck candidate0180 (37/400) (927/10000) piece0180=true := by decide +kernel
noncomputable def cell0180 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0180 accepted0180 (37/400) (927/10000) piece0180
    intervalAccepted0180 (fun t => piece_le_psi ⟨140,by decide +kernel⟩ t)
def piece0181 : AffinePiece := pieces[141]'(by decide +kernel)
theorem intervalAccepted0181 : candidateIntervalCheck candidate0181 (927/10000) (929/10000) piece0181=true := by decide +kernel
noncomputable def cell0181 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0181 accepted0181 (927/10000) (929/10000) piece0181
    intervalAccepted0181 (fun t => piece_le_psi ⟨141,by decide +kernel⟩ t)
def piece0182 : AffinePiece := pieces[142]'(by decide +kernel)
theorem intervalAccepted0182 : candidateIntervalCheck candidate0182 (929/10000) (931/10000) piece0182=true := by decide +kernel
noncomputable def cell0182 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0182 accepted0182 (929/10000) (931/10000) piece0182
    intervalAccepted0182 (fun t => piece_le_psi ⟨142,by decide +kernel⟩ t)
def piece0183 : AffinePiece := pieces[143]'(by decide +kernel)
theorem intervalAccepted0183 : candidateIntervalCheck candidate0183 (931/10000) (933/10000) piece0183=true := by decide +kernel
noncomputable def cell0183 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0183 accepted0183 (931/10000) (933/10000) piece0183
    intervalAccepted0183 (fun t => piece_le_psi ⟨143,by decide +kernel⟩ t)
def piece0184 : AffinePiece := pieces[144]'(by decide +kernel)
theorem intervalAccepted0184 : candidateIntervalCheck candidate0184 (933/10000) (187/2000) piece0184=true := by decide +kernel
noncomputable def cell0184 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0184 accepted0184 (933/10000) (187/2000) piece0184
    intervalAccepted0184 (fun t => piece_le_psi ⟨144,by decide +kernel⟩ t)
def piece0185 : AffinePiece := pieces[145]'(by decide +kernel)
theorem intervalAccepted0185 : candidateIntervalCheck candidate0185 (187/2000) (937/10000) piece0185=true := by decide +kernel
noncomputable def cell0185 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0185 accepted0185 (187/2000) (937/10000) piece0185
    intervalAccepted0185 (fun t => piece_le_psi ⟨145,by decide +kernel⟩ t)
def piece0186 : AffinePiece := pieces[146]'(by decide +kernel)
theorem intervalAccepted0186 : candidateIntervalCheck candidate0186 (937/10000) (939/10000) piece0186=true := by decide +kernel
noncomputable def cell0186 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0186 accepted0186 (937/10000) (939/10000) piece0186
    intervalAccepted0186 (fun t => piece_le_psi ⟨146,by decide +kernel⟩ t)
def piece0187 : AffinePiece := pieces[147]'(by decide +kernel)
theorem intervalAccepted0187 : candidateIntervalCheck candidate0187 (939/10000) (941/10000) piece0187=true := by decide +kernel
noncomputable def cell0187 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0187 accepted0187 (939/10000) (941/10000) piece0187
    intervalAccepted0187 (fun t => piece_le_psi ⟨147,by decide +kernel⟩ t)
def piece0188 : AffinePiece := pieces[148]'(by decide +kernel)
theorem intervalAccepted0188 : candidateIntervalCheck candidate0188 (941/10000) (943/10000) piece0188=true := by decide +kernel
noncomputable def cell0188 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0188 accepted0188 (941/10000) (943/10000) piece0188
    intervalAccepted0188 (fun t => piece_le_psi ⟨148,by decide +kernel⟩ t)
def piece0189 : AffinePiece := pieces[149]'(by decide +kernel)
theorem intervalAccepted0189 : candidateIntervalCheck candidate0189 (943/10000) (189/2000) piece0189=true := by decide +kernel
noncomputable def cell0189 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0189 accepted0189 (943/10000) (189/2000) piece0189
    intervalAccepted0189 (fun t => piece_le_psi ⟨149,by decide +kernel⟩ t)
def piece0190 : AffinePiece := pieces[150]'(by decide +kernel)
theorem intervalAccepted0190 : candidateIntervalCheck candidate0190 (189/2000) (947/10000) piece0190=true := by decide +kernel
noncomputable def cell0190 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0190 accepted0190 (189/2000) (947/10000) piece0190
    intervalAccepted0190 (fun t => piece_le_psi ⟨150,by decide +kernel⟩ t)
def piece0191 : AffinePiece := pieces[151]'(by decide +kernel)
theorem intervalAccepted0191 : candidateIntervalCheck candidate0191 (947/10000) (949/10000) piece0191=true := by decide +kernel
noncomputable def cell0191 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0191 accepted0191 (947/10000) (949/10000) piece0191
    intervalAccepted0191 (fun t => piece_le_psi ⟨151,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0176, cell0177, cell0178, cell0179, cell0180, cell0181, cell0182, cell0183, cell0184, cell0185, cell0186, cell0187, cell0188, cell0189, cell0190, cell0191]
theorem chainAccepted : spinCellChainCheck (917/10000) (949/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (917/10000) (949/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0011
