module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0002

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0002
open CandidateBatch0002 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0032 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0032 : candidateIntervalCheck candidate0032 (641/10000) (1283/20000) piece0032=true := by decide +kernel
noncomputable def cell0032 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0032 accepted0032 (641/10000) (1283/20000) piece0032
    intervalAccepted0032 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0033 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0033 : candidateIntervalCheck candidate0033 (1283/20000) (321/5000) piece0033=true := by decide +kernel
noncomputable def cell0033 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0033 accepted0033 (1283/20000) (321/5000) piece0033
    intervalAccepted0033 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0034 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0034 : candidateIntervalCheck candidate0034 (321/5000) (257/4000) piece0034=true := by decide +kernel
noncomputable def cell0034 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0034 accepted0034 (321/5000) (257/4000) piece0034
    intervalAccepted0034 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0035 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0035 : candidateIntervalCheck candidate0035 (257/4000) (643/10000) piece0035=true := by decide +kernel
noncomputable def cell0035 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0035 accepted0035 (257/4000) (643/10000) piece0035
    intervalAccepted0035 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0036 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0036 : candidateIntervalCheck candidate0036 (643/10000) (1287/20000) piece0036=true := by decide +kernel
noncomputable def cell0036 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0036 accepted0036 (643/10000) (1287/20000) piece0036
    intervalAccepted0036 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0037 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0037 : candidateIntervalCheck candidate0037 (1287/20000) (161/2500) piece0037=true := by decide +kernel
noncomputable def cell0037 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0037 accepted0037 (1287/20000) (161/2500) piece0037
    intervalAccepted0037 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0038 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0038 : candidateIntervalCheck candidate0038 (161/2500) (1289/20000) piece0038=true := by decide +kernel
noncomputable def cell0038 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0038 accepted0038 (161/2500) (1289/20000) piece0038
    intervalAccepted0038 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0039 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0039 : candidateIntervalCheck candidate0039 (1289/20000) (129/2000) piece0039=true := by decide +kernel
noncomputable def cell0039 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0039 accepted0039 (1289/20000) (129/2000) piece0039
    intervalAccepted0039 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0040 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0040 : candidateIntervalCheck candidate0040 (129/2000) (647/10000) piece0040=true := by decide +kernel
noncomputable def cell0040 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0040 accepted0040 (129/2000) (647/10000) piece0040
    intervalAccepted0040 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0041 : AffinePiece := pieces[1]'(by decide +kernel)
theorem intervalAccepted0041 : candidateIntervalCheck candidate0041 (647/10000) (649/10000) piece0041=true := by decide +kernel
noncomputable def cell0041 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0041 accepted0041 (647/10000) (649/10000) piece0041
    intervalAccepted0041 (fun t => piece_le_psi ⟨1,by decide +kernel⟩ t)
def piece0042 : AffinePiece := pieces[2]'(by decide +kernel)
theorem intervalAccepted0042 : candidateIntervalCheck candidate0042 (649/10000) (651/10000) piece0042=true := by decide +kernel
noncomputable def cell0042 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0042 accepted0042 (649/10000) (651/10000) piece0042
    intervalAccepted0042 (fun t => piece_le_psi ⟨2,by decide +kernel⟩ t)
def piece0043 : AffinePiece := pieces[3]'(by decide +kernel)
theorem intervalAccepted0043 : candidateIntervalCheck candidate0043 (651/10000) (653/10000) piece0043=true := by decide +kernel
noncomputable def cell0043 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0043 accepted0043 (651/10000) (653/10000) piece0043
    intervalAccepted0043 (fun t => piece_le_psi ⟨3,by decide +kernel⟩ t)
def piece0044 : AffinePiece := pieces[4]'(by decide +kernel)
theorem intervalAccepted0044 : candidateIntervalCheck candidate0044 (653/10000) (131/2000) piece0044=true := by decide +kernel
noncomputable def cell0044 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0044 accepted0044 (653/10000) (131/2000) piece0044
    intervalAccepted0044 (fun t => piece_le_psi ⟨4,by decide +kernel⟩ t)
def piece0045 : AffinePiece := pieces[5]'(by decide +kernel)
theorem intervalAccepted0045 : candidateIntervalCheck candidate0045 (131/2000) (657/10000) piece0045=true := by decide +kernel
noncomputable def cell0045 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0045 accepted0045 (131/2000) (657/10000) piece0045
    intervalAccepted0045 (fun t => piece_le_psi ⟨5,by decide +kernel⟩ t)
def piece0046 : AffinePiece := pieces[6]'(by decide +kernel)
theorem intervalAccepted0046 : candidateIntervalCheck candidate0046 (657/10000) (659/10000) piece0046=true := by decide +kernel
noncomputable def cell0046 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0046 accepted0046 (657/10000) (659/10000) piece0046
    intervalAccepted0046 (fun t => piece_le_psi ⟨6,by decide +kernel⟩ t)
def piece0047 : AffinePiece := pieces[7]'(by decide +kernel)
theorem intervalAccepted0047 : candidateIntervalCheck candidate0047 (659/10000) (661/10000) piece0047=true := by decide +kernel
noncomputable def cell0047 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0047 accepted0047 (659/10000) (661/10000) piece0047
    intervalAccepted0047 (fun t => piece_le_psi ⟨7,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0032, cell0033, cell0034, cell0035, cell0036, cell0037, cell0038, cell0039, cell0040, cell0041, cell0042, cell0043, cell0044, cell0045, cell0046, cell0047]
theorem chainAccepted : spinCellChainCheck (641/10000) (661/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (641/10000) (661/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0002
