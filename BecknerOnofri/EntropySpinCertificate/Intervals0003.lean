module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0003

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0003
open CandidateBatch0003 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0048 : AffinePiece := pieces[8]'(by decide +kernel)
theorem intervalAccepted0048 : candidateIntervalCheck candidate0048 (661/10000) (663/10000) piece0048=true := by decide +kernel
noncomputable def cell0048 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0048 accepted0048 (661/10000) (663/10000) piece0048
    intervalAccepted0048 (fun t => piece_le_psi ⟨8,by decide +kernel⟩ t)
def piece0049 : AffinePiece := pieces[9]'(by decide +kernel)
theorem intervalAccepted0049 : candidateIntervalCheck candidate0049 (663/10000) (133/2000) piece0049=true := by decide +kernel
noncomputable def cell0049 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0049 accepted0049 (663/10000) (133/2000) piece0049
    intervalAccepted0049 (fun t => piece_le_psi ⟨9,by decide +kernel⟩ t)
def piece0050 : AffinePiece := pieces[10]'(by decide +kernel)
theorem intervalAccepted0050 : candidateIntervalCheck candidate0050 (133/2000) (667/10000) piece0050=true := by decide +kernel
noncomputable def cell0050 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0050 accepted0050 (133/2000) (667/10000) piece0050
    intervalAccepted0050 (fun t => piece_le_psi ⟨10,by decide +kernel⟩ t)
def piece0051 : AffinePiece := pieces[11]'(by decide +kernel)
theorem intervalAccepted0051 : candidateIntervalCheck candidate0051 (667/10000) (669/10000) piece0051=true := by decide +kernel
noncomputable def cell0051 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0051 accepted0051 (667/10000) (669/10000) piece0051
    intervalAccepted0051 (fun t => piece_le_psi ⟨11,by decide +kernel⟩ t)
def piece0052 : AffinePiece := pieces[12]'(by decide +kernel)
theorem intervalAccepted0052 : candidateIntervalCheck candidate0052 (669/10000) (671/10000) piece0052=true := by decide +kernel
noncomputable def cell0052 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0052 accepted0052 (669/10000) (671/10000) piece0052
    intervalAccepted0052 (fun t => piece_le_psi ⟨12,by decide +kernel⟩ t)
def piece0053 : AffinePiece := pieces[13]'(by decide +kernel)
theorem intervalAccepted0053 : candidateIntervalCheck candidate0053 (671/10000) (673/10000) piece0053=true := by decide +kernel
noncomputable def cell0053 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0053 accepted0053 (671/10000) (673/10000) piece0053
    intervalAccepted0053 (fun t => piece_le_psi ⟨13,by decide +kernel⟩ t)
def piece0054 : AffinePiece := pieces[14]'(by decide +kernel)
theorem intervalAccepted0054 : candidateIntervalCheck candidate0054 (673/10000) (27/400) piece0054=true := by decide +kernel
noncomputable def cell0054 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0054 accepted0054 (673/10000) (27/400) piece0054
    intervalAccepted0054 (fun t => piece_le_psi ⟨14,by decide +kernel⟩ t)
def piece0055 : AffinePiece := pieces[15]'(by decide +kernel)
theorem intervalAccepted0055 : candidateIntervalCheck candidate0055 (27/400) (677/10000) piece0055=true := by decide +kernel
noncomputable def cell0055 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0055 accepted0055 (27/400) (677/10000) piece0055
    intervalAccepted0055 (fun t => piece_le_psi ⟨15,by decide +kernel⟩ t)
def piece0056 : AffinePiece := pieces[16]'(by decide +kernel)
theorem intervalAccepted0056 : candidateIntervalCheck candidate0056 (677/10000) (679/10000) piece0056=true := by decide +kernel
noncomputable def cell0056 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0056 accepted0056 (677/10000) (679/10000) piece0056
    intervalAccepted0056 (fun t => piece_le_psi ⟨16,by decide +kernel⟩ t)
def piece0057 : AffinePiece := pieces[17]'(by decide +kernel)
theorem intervalAccepted0057 : candidateIntervalCheck candidate0057 (679/10000) (681/10000) piece0057=true := by decide +kernel
noncomputable def cell0057 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0057 accepted0057 (679/10000) (681/10000) piece0057
    intervalAccepted0057 (fun t => piece_le_psi ⟨17,by decide +kernel⟩ t)
def piece0058 : AffinePiece := pieces[18]'(by decide +kernel)
theorem intervalAccepted0058 : candidateIntervalCheck candidate0058 (681/10000) (683/10000) piece0058=true := by decide +kernel
noncomputable def cell0058 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0058 accepted0058 (681/10000) (683/10000) piece0058
    intervalAccepted0058 (fun t => piece_le_psi ⟨18,by decide +kernel⟩ t)
def piece0059 : AffinePiece := pieces[19]'(by decide +kernel)
theorem intervalAccepted0059 : candidateIntervalCheck candidate0059 (683/10000) (137/2000) piece0059=true := by decide +kernel
noncomputable def cell0059 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0059 accepted0059 (683/10000) (137/2000) piece0059
    intervalAccepted0059 (fun t => piece_le_psi ⟨19,by decide +kernel⟩ t)
def piece0060 : AffinePiece := pieces[20]'(by decide +kernel)
theorem intervalAccepted0060 : candidateIntervalCheck candidate0060 (137/2000) (687/10000) piece0060=true := by decide +kernel
noncomputable def cell0060 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0060 accepted0060 (137/2000) (687/10000) piece0060
    intervalAccepted0060 (fun t => piece_le_psi ⟨20,by decide +kernel⟩ t)
def piece0061 : AffinePiece := pieces[21]'(by decide +kernel)
theorem intervalAccepted0061 : candidateIntervalCheck candidate0061 (687/10000) (689/10000) piece0061=true := by decide +kernel
noncomputable def cell0061 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0061 accepted0061 (687/10000) (689/10000) piece0061
    intervalAccepted0061 (fun t => piece_le_psi ⟨21,by decide +kernel⟩ t)
def piece0062 : AffinePiece := pieces[22]'(by decide +kernel)
theorem intervalAccepted0062 : candidateIntervalCheck candidate0062 (689/10000) (691/10000) piece0062=true := by decide +kernel
noncomputable def cell0062 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0062 accepted0062 (689/10000) (691/10000) piece0062
    intervalAccepted0062 (fun t => piece_le_psi ⟨22,by decide +kernel⟩ t)
def piece0063 : AffinePiece := pieces[23]'(by decide +kernel)
theorem intervalAccepted0063 : candidateIntervalCheck candidate0063 (691/10000) (693/10000) piece0063=true := by decide +kernel
noncomputable def cell0063 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0063 accepted0063 (691/10000) (693/10000) piece0063
    intervalAccepted0063 (fun t => piece_le_psi ⟨23,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0048, cell0049, cell0050, cell0051, cell0052, cell0053, cell0054, cell0055, cell0056, cell0057, cell0058, cell0059, cell0060, cell0061, cell0062, cell0063]
theorem chainAccepted : spinCellChainCheck (661/10000) (693/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (661/10000) (693/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0003
