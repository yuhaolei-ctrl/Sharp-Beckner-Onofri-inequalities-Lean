module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0062

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0062
open CandidateBatch0062 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0992 : AffinePiece := pieces[890]'(by decide +kernel)
theorem intervalAccepted0992 : candidateIntervalCheck candidate0992 (237/500) (19/40) piece0992=true := by decide +kernel
noncomputable def cell0992 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0992 accepted0992 (237/500) (19/40) piece0992
    intervalAccepted0992 (fun t => piece_le_psi ⟨890,by decide +kernel⟩ t)
def piece0993 : AffinePiece := pieces[891]'(by decide +kernel)
theorem intervalAccepted0993 : candidateIntervalCheck candidate0993 (19/40) (119/250) piece0993=true := by decide +kernel
noncomputable def cell0993 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0993 accepted0993 (19/40) (119/250) piece0993
    intervalAccepted0993 (fun t => piece_le_psi ⟨891,by decide +kernel⟩ t)
def piece0994 : AffinePiece := pieces[892]'(by decide +kernel)
theorem intervalAccepted0994 : candidateIntervalCheck candidate0994 (119/250) (477/1000) piece0994=true := by decide +kernel
noncomputable def cell0994 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0994 accepted0994 (119/250) (477/1000) piece0994
    intervalAccepted0994 (fun t => piece_le_psi ⟨892,by decide +kernel⟩ t)
def piece0995 : AffinePiece := pieces[893]'(by decide +kernel)
theorem intervalAccepted0995 : candidateIntervalCheck candidate0995 (477/1000) (239/500) piece0995=true := by decide +kernel
noncomputable def cell0995 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0995 accepted0995 (477/1000) (239/500) piece0995
    intervalAccepted0995 (fun t => piece_le_psi ⟨893,by decide +kernel⟩ t)
def piece0996 : AffinePiece := pieces[894]'(by decide +kernel)
theorem intervalAccepted0996 : candidateIntervalCheck candidate0996 (239/500) (479/1000) piece0996=true := by decide +kernel
noncomputable def cell0996 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0996 accepted0996 (239/500) (479/1000) piece0996
    intervalAccepted0996 (fun t => piece_le_psi ⟨894,by decide +kernel⟩ t)
def piece0997 : AffinePiece := pieces[895]'(by decide +kernel)
theorem intervalAccepted0997 : candidateIntervalCheck candidate0997 (479/1000) (12/25) piece0997=true := by decide +kernel
noncomputable def cell0997 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0997 accepted0997 (479/1000) (12/25) piece0997
    intervalAccepted0997 (fun t => piece_le_psi ⟨895,by decide +kernel⟩ t)
def piece0998 : AffinePiece := pieces[896]'(by decide +kernel)
theorem intervalAccepted0998 : candidateIntervalCheck candidate0998 (12/25) (481/1000) piece0998=true := by decide +kernel
noncomputable def cell0998 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0998 accepted0998 (12/25) (481/1000) piece0998
    intervalAccepted0998 (fun t => piece_le_psi ⟨896,by decide +kernel⟩ t)
def piece0999 : AffinePiece := pieces[897]'(by decide +kernel)
theorem intervalAccepted0999 : candidateIntervalCheck candidate0999 (481/1000) (241/500) piece0999=true := by decide +kernel
noncomputable def cell0999 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0999 accepted0999 (481/1000) (241/500) piece0999
    intervalAccepted0999 (fun t => piece_le_psi ⟨897,by decide +kernel⟩ t)
def piece1000 : AffinePiece := pieces[898]'(by decide +kernel)
theorem intervalAccepted1000 : candidateIntervalCheck candidate1000 (241/500) (483/1000) piece1000=true := by decide +kernel
noncomputable def cell1000 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1000 accepted1000 (241/500) (483/1000) piece1000
    intervalAccepted1000 (fun t => piece_le_psi ⟨898,by decide +kernel⟩ t)
def piece1001 : AffinePiece := pieces[899]'(by decide +kernel)
theorem intervalAccepted1001 : candidateIntervalCheck candidate1001 (483/1000) (121/250) piece1001=true := by decide +kernel
noncomputable def cell1001 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1001 accepted1001 (483/1000) (121/250) piece1001
    intervalAccepted1001 (fun t => piece_le_psi ⟨899,by decide +kernel⟩ t)
def piece1002 : AffinePiece := pieces[900]'(by decide +kernel)
theorem intervalAccepted1002 : candidateIntervalCheck candidate1002 (121/250) (97/200) piece1002=true := by decide +kernel
noncomputable def cell1002 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1002 accepted1002 (121/250) (97/200) piece1002
    intervalAccepted1002 (fun t => piece_le_psi ⟨900,by decide +kernel⟩ t)
def piece1003 : AffinePiece := pieces[901]'(by decide +kernel)
theorem intervalAccepted1003 : candidateIntervalCheck candidate1003 (97/200) (243/500) piece1003=true := by decide +kernel
noncomputable def cell1003 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1003 accepted1003 (97/200) (243/500) piece1003
    intervalAccepted1003 (fun t => piece_le_psi ⟨901,by decide +kernel⟩ t)
def piece1004 : AffinePiece := pieces[902]'(by decide +kernel)
theorem intervalAccepted1004 : candidateIntervalCheck candidate1004 (243/500) (487/1000) piece1004=true := by decide +kernel
noncomputable def cell1004 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1004 accepted1004 (243/500) (487/1000) piece1004
    intervalAccepted1004 (fun t => piece_le_psi ⟨902,by decide +kernel⟩ t)
def piece1005 : AffinePiece := pieces[903]'(by decide +kernel)
theorem intervalAccepted1005 : candidateIntervalCheck candidate1005 (487/1000) (61/125) piece1005=true := by decide +kernel
noncomputable def cell1005 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1005 accepted1005 (487/1000) (61/125) piece1005
    intervalAccepted1005 (fun t => piece_le_psi ⟨903,by decide +kernel⟩ t)
def piece1006 : AffinePiece := pieces[904]'(by decide +kernel)
theorem intervalAccepted1006 : candidateIntervalCheck candidate1006 (61/125) (489/1000) piece1006=true := by decide +kernel
noncomputable def cell1006 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1006 accepted1006 (61/125) (489/1000) piece1006
    intervalAccepted1006 (fun t => piece_le_psi ⟨904,by decide +kernel⟩ t)
def piece1007 : AffinePiece := pieces[905]'(by decide +kernel)
theorem intervalAccepted1007 : candidateIntervalCheck candidate1007 (489/1000) (49/100) piece1007=true := by decide +kernel
noncomputable def cell1007 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1007 accepted1007 (489/1000) (49/100) piece1007
    intervalAccepted1007 (fun t => piece_le_psi ⟨905,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0992, cell0993, cell0994, cell0995, cell0996, cell0997, cell0998, cell0999, cell1000, cell1001, cell1002, cell1003, cell1004, cell1005, cell1006, cell1007]
theorem chainAccepted : spinCellChainCheck (237/500) (49/100) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (237/500) (49/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0062
