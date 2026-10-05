module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0010

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0010
open CandidateBatch0010 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0160 : AffinePiece := pieces[120]'(by decide +kernel)
theorem intervalAccepted0160 : candidateIntervalCheck candidate0160 (177/2000) (887/10000) piece0160=true := by decide +kernel
noncomputable def cell0160 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0160 accepted0160 (177/2000) (887/10000) piece0160
    intervalAccepted0160 (fun t => piece_le_psi ⟨120,by decide +kernel⟩ t)
def piece0161 : AffinePiece := pieces[121]'(by decide +kernel)
theorem intervalAccepted0161 : candidateIntervalCheck candidate0161 (887/10000) (889/10000) piece0161=true := by decide +kernel
noncomputable def cell0161 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0161 accepted0161 (887/10000) (889/10000) piece0161
    intervalAccepted0161 (fun t => piece_le_psi ⟨121,by decide +kernel⟩ t)
def piece0162 : AffinePiece := pieces[122]'(by decide +kernel)
theorem intervalAccepted0162 : candidateIntervalCheck candidate0162 (889/10000) (891/10000) piece0162=true := by decide +kernel
noncomputable def cell0162 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0162 accepted0162 (889/10000) (891/10000) piece0162
    intervalAccepted0162 (fun t => piece_le_psi ⟨122,by decide +kernel⟩ t)
def piece0163 : AffinePiece := pieces[123]'(by decide +kernel)
theorem intervalAccepted0163 : candidateIntervalCheck candidate0163 (891/10000) (893/10000) piece0163=true := by decide +kernel
noncomputable def cell0163 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0163 accepted0163 (891/10000) (893/10000) piece0163
    intervalAccepted0163 (fun t => piece_le_psi ⟨123,by decide +kernel⟩ t)
def piece0164 : AffinePiece := pieces[124]'(by decide +kernel)
theorem intervalAccepted0164 : candidateIntervalCheck candidate0164 (893/10000) (179/2000) piece0164=true := by decide +kernel
noncomputable def cell0164 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0164 accepted0164 (893/10000) (179/2000) piece0164
    intervalAccepted0164 (fun t => piece_le_psi ⟨124,by decide +kernel⟩ t)
def piece0165 : AffinePiece := pieces[125]'(by decide +kernel)
theorem intervalAccepted0165 : candidateIntervalCheck candidate0165 (179/2000) (897/10000) piece0165=true := by decide +kernel
noncomputable def cell0165 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0165 accepted0165 (179/2000) (897/10000) piece0165
    intervalAccepted0165 (fun t => piece_le_psi ⟨125,by decide +kernel⟩ t)
def piece0166 : AffinePiece := pieces[126]'(by decide +kernel)
theorem intervalAccepted0166 : candidateIntervalCheck candidate0166 (897/10000) (899/10000) piece0166=true := by decide +kernel
noncomputable def cell0166 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0166 accepted0166 (897/10000) (899/10000) piece0166
    intervalAccepted0166 (fun t => piece_le_psi ⟨126,by decide +kernel⟩ t)
def piece0167 : AffinePiece := pieces[127]'(by decide +kernel)
theorem intervalAccepted0167 : candidateIntervalCheck candidate0167 (899/10000) (901/10000) piece0167=true := by decide +kernel
noncomputable def cell0167 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0167 accepted0167 (899/10000) (901/10000) piece0167
    intervalAccepted0167 (fun t => piece_le_psi ⟨127,by decide +kernel⟩ t)
def piece0168 : AffinePiece := pieces[128]'(by decide +kernel)
theorem intervalAccepted0168 : candidateIntervalCheck candidate0168 (901/10000) (903/10000) piece0168=true := by decide +kernel
noncomputable def cell0168 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0168 accepted0168 (901/10000) (903/10000) piece0168
    intervalAccepted0168 (fun t => piece_le_psi ⟨128,by decide +kernel⟩ t)
def piece0169 : AffinePiece := pieces[129]'(by decide +kernel)
theorem intervalAccepted0169 : candidateIntervalCheck candidate0169 (903/10000) (181/2000) piece0169=true := by decide +kernel
noncomputable def cell0169 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0169 accepted0169 (903/10000) (181/2000) piece0169
    intervalAccepted0169 (fun t => piece_le_psi ⟨129,by decide +kernel⟩ t)
def piece0170 : AffinePiece := pieces[130]'(by decide +kernel)
theorem intervalAccepted0170 : candidateIntervalCheck candidate0170 (181/2000) (907/10000) piece0170=true := by decide +kernel
noncomputable def cell0170 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0170 accepted0170 (181/2000) (907/10000) piece0170
    intervalAccepted0170 (fun t => piece_le_psi ⟨130,by decide +kernel⟩ t)
def piece0171 : AffinePiece := pieces[131]'(by decide +kernel)
theorem intervalAccepted0171 : candidateIntervalCheck candidate0171 (907/10000) (909/10000) piece0171=true := by decide +kernel
noncomputable def cell0171 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0171 accepted0171 (907/10000) (909/10000) piece0171
    intervalAccepted0171 (fun t => piece_le_psi ⟨131,by decide +kernel⟩ t)
def piece0172 : AffinePiece := pieces[132]'(by decide +kernel)
theorem intervalAccepted0172 : candidateIntervalCheck candidate0172 (909/10000) (911/10000) piece0172=true := by decide +kernel
noncomputable def cell0172 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0172 accepted0172 (909/10000) (911/10000) piece0172
    intervalAccepted0172 (fun t => piece_le_psi ⟨132,by decide +kernel⟩ t)
def piece0173 : AffinePiece := pieces[133]'(by decide +kernel)
theorem intervalAccepted0173 : candidateIntervalCheck candidate0173 (911/10000) (913/10000) piece0173=true := by decide +kernel
noncomputable def cell0173 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0173 accepted0173 (911/10000) (913/10000) piece0173
    intervalAccepted0173 (fun t => piece_le_psi ⟨133,by decide +kernel⟩ t)
def piece0174 : AffinePiece := pieces[134]'(by decide +kernel)
theorem intervalAccepted0174 : candidateIntervalCheck candidate0174 (913/10000) (183/2000) piece0174=true := by decide +kernel
noncomputable def cell0174 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0174 accepted0174 (913/10000) (183/2000) piece0174
    intervalAccepted0174 (fun t => piece_le_psi ⟨134,by decide +kernel⟩ t)
def piece0175 : AffinePiece := pieces[135]'(by decide +kernel)
theorem intervalAccepted0175 : candidateIntervalCheck candidate0175 (183/2000) (917/10000) piece0175=true := by decide +kernel
noncomputable def cell0175 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0175 accepted0175 (183/2000) (917/10000) piece0175
    intervalAccepted0175 (fun t => piece_le_psi ⟨135,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0160, cell0161, cell0162, cell0163, cell0164, cell0165, cell0166, cell0167, cell0168, cell0169, cell0170, cell0171, cell0172, cell0173, cell0174, cell0175]
theorem chainAccepted : spinCellChainCheck (177/2000) (917/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (177/2000) (917/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0010
