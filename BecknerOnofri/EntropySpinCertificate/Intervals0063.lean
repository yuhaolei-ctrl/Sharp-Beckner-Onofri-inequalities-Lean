module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0063

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0063
open CandidateBatch0063 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1008 : AffinePiece := pieces[906]'(by decide +kernel)
theorem intervalAccepted1008 : candidateIntervalCheck candidate1008 (49/100) (491/1000) piece1008=true := by decide +kernel
noncomputable def cell1008 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1008 accepted1008 (49/100) (491/1000) piece1008
    intervalAccepted1008 (fun t => piece_le_psi ⟨906,by decide +kernel⟩ t)
def piece1009 : AffinePiece := pieces[907]'(by decide +kernel)
theorem intervalAccepted1009 : candidateIntervalCheck candidate1009 (491/1000) (123/250) piece1009=true := by decide +kernel
noncomputable def cell1009 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1009 accepted1009 (491/1000) (123/250) piece1009
    intervalAccepted1009 (fun t => piece_le_psi ⟨907,by decide +kernel⟩ t)
def piece1010 : AffinePiece := pieces[908]'(by decide +kernel)
theorem intervalAccepted1010 : candidateIntervalCheck candidate1010 (123/250) (493/1000) piece1010=true := by decide +kernel
noncomputable def cell1010 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1010 accepted1010 (123/250) (493/1000) piece1010
    intervalAccepted1010 (fun t => piece_le_psi ⟨908,by decide +kernel⟩ t)
def piece1011 : AffinePiece := pieces[909]'(by decide +kernel)
theorem intervalAccepted1011 : candidateIntervalCheck candidate1011 (493/1000) (247/500) piece1011=true := by decide +kernel
noncomputable def cell1011 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1011 accepted1011 (493/1000) (247/500) piece1011
    intervalAccepted1011 (fun t => piece_le_psi ⟨909,by decide +kernel⟩ t)
def piece1012 : AffinePiece := pieces[910]'(by decide +kernel)
theorem intervalAccepted1012 : candidateIntervalCheck candidate1012 (247/500) (99/200) piece1012=true := by decide +kernel
noncomputable def cell1012 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1012 accepted1012 (247/500) (99/200) piece1012
    intervalAccepted1012 (fun t => piece_le_psi ⟨910,by decide +kernel⟩ t)
def piece1013 : AffinePiece := pieces[911]'(by decide +kernel)
theorem intervalAccepted1013 : candidateIntervalCheck candidate1013 (99/200) (62/125) piece1013=true := by decide +kernel
noncomputable def cell1013 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1013 accepted1013 (99/200) (62/125) piece1013
    intervalAccepted1013 (fun t => piece_le_psi ⟨911,by decide +kernel⟩ t)
def piece1014 : AffinePiece := pieces[912]'(by decide +kernel)
theorem intervalAccepted1014 : candidateIntervalCheck candidate1014 (62/125) (497/1000) piece1014=true := by decide +kernel
noncomputable def cell1014 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1014 accepted1014 (62/125) (497/1000) piece1014
    intervalAccepted1014 (fun t => piece_le_psi ⟨912,by decide +kernel⟩ t)
def piece1015 : AffinePiece := pieces[913]'(by decide +kernel)
theorem intervalAccepted1015 : candidateIntervalCheck candidate1015 (497/1000) (249/500) piece1015=true := by decide +kernel
noncomputable def cell1015 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1015 accepted1015 (497/1000) (249/500) piece1015
    intervalAccepted1015 (fun t => piece_le_psi ⟨913,by decide +kernel⟩ t)
def piece1016 : AffinePiece := pieces[914]'(by decide +kernel)
theorem intervalAccepted1016 : candidateIntervalCheck candidate1016 (249/500) (499/1000) piece1016=true := by decide +kernel
noncomputable def cell1016 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1016 accepted1016 (249/500) (499/1000) piece1016
    intervalAccepted1016 (fun t => piece_le_psi ⟨914,by decide +kernel⟩ t)
def piece1017 : AffinePiece := pieces[915]'(by decide +kernel)
theorem intervalAccepted1017 : candidateIntervalCheck candidate1017 (499/1000) (1/2) piece1017=true := by decide +kernel
noncomputable def cell1017 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1017 accepted1017 (499/1000) (1/2) piece1017
    intervalAccepted1017 (fun t => piece_le_psi ⟨915,by decide +kernel⟩ t)
def piece1018 : AffinePiece := pieces[916]'(by decide +kernel)
theorem intervalAccepted1018 : candidateIntervalCheck candidate1018 (1/2) (501/1000) piece1018=true := by decide +kernel
noncomputable def cell1018 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1018 accepted1018 (1/2) (501/1000) piece1018
    intervalAccepted1018 (fun t => piece_le_psi ⟨916,by decide +kernel⟩ t)
def piece1019 : AffinePiece := pieces[917]'(by decide +kernel)
theorem intervalAccepted1019 : candidateIntervalCheck candidate1019 (501/1000) (251/500) piece1019=true := by decide +kernel
noncomputable def cell1019 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1019 accepted1019 (501/1000) (251/500) piece1019
    intervalAccepted1019 (fun t => piece_le_psi ⟨917,by decide +kernel⟩ t)
def piece1020 : AffinePiece := pieces[918]'(by decide +kernel)
theorem intervalAccepted1020 : candidateIntervalCheck candidate1020 (251/500) (503/1000) piece1020=true := by decide +kernel
noncomputable def cell1020 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1020 accepted1020 (251/500) (503/1000) piece1020
    intervalAccepted1020 (fun t => piece_le_psi ⟨918,by decide +kernel⟩ t)
def piece1021 : AffinePiece := pieces[919]'(by decide +kernel)
theorem intervalAccepted1021 : candidateIntervalCheck candidate1021 (503/1000) (63/125) piece1021=true := by decide +kernel
noncomputable def cell1021 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1021 accepted1021 (503/1000) (63/125) piece1021
    intervalAccepted1021 (fun t => piece_le_psi ⟨919,by decide +kernel⟩ t)
def piece1022 : AffinePiece := pieces[920]'(by decide +kernel)
theorem intervalAccepted1022 : candidateIntervalCheck candidate1022 (63/125) (101/200) piece1022=true := by decide +kernel
noncomputable def cell1022 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1022 accepted1022 (63/125) (101/200) piece1022
    intervalAccepted1022 (fun t => piece_le_psi ⟨920,by decide +kernel⟩ t)
def piece1023 : AffinePiece := pieces[921]'(by decide +kernel)
theorem intervalAccepted1023 : candidateIntervalCheck candidate1023 (101/200) (253/500) piece1023=true := by decide +kernel
noncomputable def cell1023 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1023 accepted1023 (101/200) (253/500) piece1023
    intervalAccepted1023 (fun t => piece_le_psi ⟨921,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1008, cell1009, cell1010, cell1011, cell1012, cell1013, cell1014, cell1015, cell1016, cell1017, cell1018, cell1019, cell1020, cell1021, cell1022, cell1023]
theorem chainAccepted : spinCellChainCheck (49/100) (253/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (49/100) (253/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0063
