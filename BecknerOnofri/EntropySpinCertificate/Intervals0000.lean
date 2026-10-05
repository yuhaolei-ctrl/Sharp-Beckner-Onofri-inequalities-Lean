import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0000
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0000
open CandidateBatch0000 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0000 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0000 : candidateIntervalCheck candidate0000 (1/16) (1251/20000) piece0000=true := by decide +kernel
noncomputable def cell0000 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0000 accepted0000 (1/16) (1251/20000) piece0000
    intervalAccepted0000 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0001 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0001 : candidateIntervalCheck candidate0001 (1251/20000) (313/5000) piece0001=true := by decide +kernel
noncomputable def cell0001 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0001 accepted0001 (1251/20000) (313/5000) piece0001
    intervalAccepted0001 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0002 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0002 : candidateIntervalCheck candidate0002 (313/5000) (1253/20000) piece0002=true := by decide +kernel
noncomputable def cell0002 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0002 accepted0002 (313/5000) (1253/20000) piece0002
    intervalAccepted0002 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0003 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0003 : candidateIntervalCheck candidate0003 (1253/20000) (627/10000) piece0003=true := by decide +kernel
noncomputable def cell0003 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0003 accepted0003 (1253/20000) (627/10000) piece0003
    intervalAccepted0003 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0004 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0004 : candidateIntervalCheck candidate0004 (627/10000) (251/4000) piece0004=true := by decide +kernel
noncomputable def cell0004 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0004 accepted0004 (627/10000) (251/4000) piece0004
    intervalAccepted0004 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0005 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0005 : candidateIntervalCheck candidate0005 (251/4000) (157/2500) piece0005=true := by decide +kernel
noncomputable def cell0005 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0005 accepted0005 (251/4000) (157/2500) piece0005
    intervalAccepted0005 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0006 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0006 : candidateIntervalCheck candidate0006 (157/2500) (1257/20000) piece0006=true := by decide +kernel
noncomputable def cell0006 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0006 accepted0006 (157/2500) (1257/20000) piece0006
    intervalAccepted0006 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0007 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0007 : candidateIntervalCheck candidate0007 (1257/20000) (629/10000) piece0007=true := by decide +kernel
noncomputable def cell0007 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0007 accepted0007 (1257/20000) (629/10000) piece0007
    intervalAccepted0007 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0008 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0008 : candidateIntervalCheck candidate0008 (629/10000) (1259/20000) piece0008=true := by decide +kernel
noncomputable def cell0008 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0008 accepted0008 (629/10000) (1259/20000) piece0008
    intervalAccepted0008 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0009 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0009 : candidateIntervalCheck candidate0009 (1259/20000) (63/1000) piece0009=true := by decide +kernel
noncomputable def cell0009 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0009 accepted0009 (1259/20000) (63/1000) piece0009
    intervalAccepted0009 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0010 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0010 : candidateIntervalCheck candidate0010 (63/1000) (1261/20000) piece0010=true := by decide +kernel
noncomputable def cell0010 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0010 accepted0010 (63/1000) (1261/20000) piece0010
    intervalAccepted0010 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0011 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0011 : candidateIntervalCheck candidate0011 (1261/20000) (631/10000) piece0011=true := by decide +kernel
noncomputable def cell0011 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0011 accepted0011 (1261/20000) (631/10000) piece0011
    intervalAccepted0011 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0012 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0012 : candidateIntervalCheck candidate0012 (631/10000) (1263/20000) piece0012=true := by decide +kernel
noncomputable def cell0012 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0012 accepted0012 (631/10000) (1263/20000) piece0012
    intervalAccepted0012 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0013 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0013 : candidateIntervalCheck candidate0013 (1263/20000) (79/1250) piece0013=true := by decide +kernel
noncomputable def cell0013 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0013 accepted0013 (1263/20000) (79/1250) piece0013
    intervalAccepted0013 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0014 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0014 : candidateIntervalCheck candidate0014 (79/1250) (253/4000) piece0014=true := by decide +kernel
noncomputable def cell0014 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0014 accepted0014 (79/1250) (253/4000) piece0014
    intervalAccepted0014 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0015 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0015 : candidateIntervalCheck candidate0015 (253/4000) (633/10000) piece0015=true := by decide +kernel
noncomputable def cell0015 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0015 accepted0015 (253/4000) (633/10000) piece0015
    intervalAccepted0015 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0000, cell0001, cell0002, cell0003, cell0004, cell0005, cell0006, cell0007, cell0008, cell0009, cell0010, cell0011, cell0012, cell0013, cell0014, cell0015]
theorem chainAccepted : spinCellChainCheck (1/16) (633/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1/16) (633/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0000
