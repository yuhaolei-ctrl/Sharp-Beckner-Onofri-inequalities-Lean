import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0064
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0064
open CandidateBatch0064 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1024 : AffinePiece := pieces[922]'(by decide +kernel)
theorem intervalAccepted1024 : candidateIntervalCheck candidate1024 (253/500) (507/1000) piece1024=true := by decide +kernel
noncomputable def cell1024 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1024 accepted1024 (253/500) (507/1000) piece1024
    intervalAccepted1024 (fun t => piece_le_psi ⟨922,by decide +kernel⟩ t)
def piece1025 : AffinePiece := pieces[923]'(by decide +kernel)
theorem intervalAccepted1025 : candidateIntervalCheck candidate1025 (507/1000) (127/250) piece1025=true := by decide +kernel
noncomputable def cell1025 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1025 accepted1025 (507/1000) (127/250) piece1025
    intervalAccepted1025 (fun t => piece_le_psi ⟨923,by decide +kernel⟩ t)
def piece1026 : AffinePiece := pieces[924]'(by decide +kernel)
theorem intervalAccepted1026 : candidateIntervalCheck candidate1026 (127/250) (509/1000) piece1026=true := by decide +kernel
noncomputable def cell1026 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1026 accepted1026 (127/250) (509/1000) piece1026
    intervalAccepted1026 (fun t => piece_le_psi ⟨924,by decide +kernel⟩ t)
def piece1027 : AffinePiece := pieces[925]'(by decide +kernel)
theorem intervalAccepted1027 : candidateIntervalCheck candidate1027 (509/1000) (51/100) piece1027=true := by decide +kernel
noncomputable def cell1027 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1027 accepted1027 (509/1000) (51/100) piece1027
    intervalAccepted1027 (fun t => piece_le_psi ⟨925,by decide +kernel⟩ t)
def piece1028 : AffinePiece := pieces[926]'(by decide +kernel)
theorem intervalAccepted1028 : candidateIntervalCheck candidate1028 (51/100) (511/1000) piece1028=true := by decide +kernel
noncomputable def cell1028 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1028 accepted1028 (51/100) (511/1000) piece1028
    intervalAccepted1028 (fun t => piece_le_psi ⟨926,by decide +kernel⟩ t)
def piece1029 : AffinePiece := pieces[927]'(by decide +kernel)
theorem intervalAccepted1029 : candidateIntervalCheck candidate1029 (511/1000) (64/125) piece1029=true := by decide +kernel
noncomputable def cell1029 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1029 accepted1029 (511/1000) (64/125) piece1029
    intervalAccepted1029 (fun t => piece_le_psi ⟨927,by decide +kernel⟩ t)
def piece1030 : AffinePiece := pieces[928]'(by decide +kernel)
theorem intervalAccepted1030 : candidateIntervalCheck candidate1030 (64/125) (513/1000) piece1030=true := by decide +kernel
noncomputable def cell1030 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1030 accepted1030 (64/125) (513/1000) piece1030
    intervalAccepted1030 (fun t => piece_le_psi ⟨928,by decide +kernel⟩ t)
def piece1031 : AffinePiece := pieces[929]'(by decide +kernel)
theorem intervalAccepted1031 : candidateIntervalCheck candidate1031 (513/1000) (257/500) piece1031=true := by decide +kernel
noncomputable def cell1031 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1031 accepted1031 (513/1000) (257/500) piece1031
    intervalAccepted1031 (fun t => piece_le_psi ⟨929,by decide +kernel⟩ t)
def piece1032 : AffinePiece := pieces[930]'(by decide +kernel)
theorem intervalAccepted1032 : candidateIntervalCheck candidate1032 (257/500) (103/200) piece1032=true := by decide +kernel
noncomputable def cell1032 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1032 accepted1032 (257/500) (103/200) piece1032
    intervalAccepted1032 (fun t => piece_le_psi ⟨930,by decide +kernel⟩ t)
def piece1033 : AffinePiece := pieces[931]'(by decide +kernel)
theorem intervalAccepted1033 : candidateIntervalCheck candidate1033 (103/200) (129/250) piece1033=true := by decide +kernel
noncomputable def cell1033 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1033 accepted1033 (103/200) (129/250) piece1033
    intervalAccepted1033 (fun t => piece_le_psi ⟨931,by decide +kernel⟩ t)
def piece1034 : AffinePiece := pieces[932]'(by decide +kernel)
theorem intervalAccepted1034 : candidateIntervalCheck candidate1034 (129/250) (517/1000) piece1034=true := by decide +kernel
noncomputable def cell1034 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1034 accepted1034 (129/250) (517/1000) piece1034
    intervalAccepted1034 (fun t => piece_le_psi ⟨932,by decide +kernel⟩ t)
def piece1035 : AffinePiece := pieces[933]'(by decide +kernel)
theorem intervalAccepted1035 : candidateIntervalCheck candidate1035 (517/1000) (259/500) piece1035=true := by decide +kernel
noncomputable def cell1035 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1035 accepted1035 (517/1000) (259/500) piece1035
    intervalAccepted1035 (fun t => piece_le_psi ⟨933,by decide +kernel⟩ t)
def piece1036 : AffinePiece := pieces[934]'(by decide +kernel)
theorem intervalAccepted1036 : candidateIntervalCheck candidate1036 (259/500) (519/1000) piece1036=true := by decide +kernel
noncomputable def cell1036 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1036 accepted1036 (259/500) (519/1000) piece1036
    intervalAccepted1036 (fun t => piece_le_psi ⟨934,by decide +kernel⟩ t)
def piece1037 : AffinePiece := pieces[935]'(by decide +kernel)
theorem intervalAccepted1037 : candidateIntervalCheck candidate1037 (519/1000) (13/25) piece1037=true := by decide +kernel
noncomputable def cell1037 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1037 accepted1037 (519/1000) (13/25) piece1037
    intervalAccepted1037 (fun t => piece_le_psi ⟨935,by decide +kernel⟩ t)
def piece1038 : AffinePiece := pieces[936]'(by decide +kernel)
theorem intervalAccepted1038 : candidateIntervalCheck candidate1038 (13/25) (521/1000) piece1038=true := by decide +kernel
noncomputable def cell1038 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1038 accepted1038 (13/25) (521/1000) piece1038
    intervalAccepted1038 (fun t => piece_le_psi ⟨936,by decide +kernel⟩ t)
def piece1039 : AffinePiece := pieces[937]'(by decide +kernel)
theorem intervalAccepted1039 : candidateIntervalCheck candidate1039 (521/1000) (261/500) piece1039=true := by decide +kernel
noncomputable def cell1039 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1039 accepted1039 (521/1000) (261/500) piece1039
    intervalAccepted1039 (fun t => piece_le_psi ⟨937,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1024, cell1025, cell1026, cell1027, cell1028, cell1029, cell1030, cell1031, cell1032, cell1033, cell1034, cell1035, cell1036, cell1037, cell1038, cell1039]
theorem chainAccepted : spinCellChainCheck (253/500) (261/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (253/500) (261/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0064
