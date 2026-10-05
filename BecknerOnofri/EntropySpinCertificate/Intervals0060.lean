import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0060
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0060
open CandidateBatch0060 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0960 : AffinePiece := pieces[858]'(by decide +kernel)
theorem intervalAccepted0960 : candidateIntervalCheck candidate0960 (221/500) (443/1000) piece0960=true := by decide +kernel
noncomputable def cell0960 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0960 accepted0960 (221/500) (443/1000) piece0960
    intervalAccepted0960 (fun t => piece_le_psi ⟨858,by decide +kernel⟩ t)
def piece0961 : AffinePiece := pieces[859]'(by decide +kernel)
theorem intervalAccepted0961 : candidateIntervalCheck candidate0961 (443/1000) (111/250) piece0961=true := by decide +kernel
noncomputable def cell0961 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0961 accepted0961 (443/1000) (111/250) piece0961
    intervalAccepted0961 (fun t => piece_le_psi ⟨859,by decide +kernel⟩ t)
def piece0962 : AffinePiece := pieces[860]'(by decide +kernel)
theorem intervalAccepted0962 : candidateIntervalCheck candidate0962 (111/250) (89/200) piece0962=true := by decide +kernel
noncomputable def cell0962 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0962 accepted0962 (111/250) (89/200) piece0962
    intervalAccepted0962 (fun t => piece_le_psi ⟨860,by decide +kernel⟩ t)
def piece0963 : AffinePiece := pieces[861]'(by decide +kernel)
theorem intervalAccepted0963 : candidateIntervalCheck candidate0963 (89/200) (223/500) piece0963=true := by decide +kernel
noncomputable def cell0963 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0963 accepted0963 (89/200) (223/500) piece0963
    intervalAccepted0963 (fun t => piece_le_psi ⟨861,by decide +kernel⟩ t)
def piece0964 : AffinePiece := pieces[862]'(by decide +kernel)
theorem intervalAccepted0964 : candidateIntervalCheck candidate0964 (223/500) (447/1000) piece0964=true := by decide +kernel
noncomputable def cell0964 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0964 accepted0964 (223/500) (447/1000) piece0964
    intervalAccepted0964 (fun t => piece_le_psi ⟨862,by decide +kernel⟩ t)
def piece0965 : AffinePiece := pieces[863]'(by decide +kernel)
theorem intervalAccepted0965 : candidateIntervalCheck candidate0965 (447/1000) (56/125) piece0965=true := by decide +kernel
noncomputable def cell0965 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0965 accepted0965 (447/1000) (56/125) piece0965
    intervalAccepted0965 (fun t => piece_le_psi ⟨863,by decide +kernel⟩ t)
def piece0966 : AffinePiece := pieces[864]'(by decide +kernel)
theorem intervalAccepted0966 : candidateIntervalCheck candidate0966 (56/125) (449/1000) piece0966=true := by decide +kernel
noncomputable def cell0966 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0966 accepted0966 (56/125) (449/1000) piece0966
    intervalAccepted0966 (fun t => piece_le_psi ⟨864,by decide +kernel⟩ t)
def piece0967 : AffinePiece := pieces[865]'(by decide +kernel)
theorem intervalAccepted0967 : candidateIntervalCheck candidate0967 (449/1000) (9/20) piece0967=true := by decide +kernel
noncomputable def cell0967 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0967 accepted0967 (449/1000) (9/20) piece0967
    intervalAccepted0967 (fun t => piece_le_psi ⟨865,by decide +kernel⟩ t)
def piece0968 : AffinePiece := pieces[866]'(by decide +kernel)
theorem intervalAccepted0968 : candidateIntervalCheck candidate0968 (9/20) (451/1000) piece0968=true := by decide +kernel
noncomputable def cell0968 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0968 accepted0968 (9/20) (451/1000) piece0968
    intervalAccepted0968 (fun t => piece_le_psi ⟨866,by decide +kernel⟩ t)
def piece0969 : AffinePiece := pieces[867]'(by decide +kernel)
theorem intervalAccepted0969 : candidateIntervalCheck candidate0969 (451/1000) (113/250) piece0969=true := by decide +kernel
noncomputable def cell0969 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0969 accepted0969 (451/1000) (113/250) piece0969
    intervalAccepted0969 (fun t => piece_le_psi ⟨867,by decide +kernel⟩ t)
def piece0970 : AffinePiece := pieces[868]'(by decide +kernel)
theorem intervalAccepted0970 : candidateIntervalCheck candidate0970 (113/250) (453/1000) piece0970=true := by decide +kernel
noncomputable def cell0970 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0970 accepted0970 (113/250) (453/1000) piece0970
    intervalAccepted0970 (fun t => piece_le_psi ⟨868,by decide +kernel⟩ t)
def piece0971 : AffinePiece := pieces[869]'(by decide +kernel)
theorem intervalAccepted0971 : candidateIntervalCheck candidate0971 (453/1000) (227/500) piece0971=true := by decide +kernel
noncomputable def cell0971 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0971 accepted0971 (453/1000) (227/500) piece0971
    intervalAccepted0971 (fun t => piece_le_psi ⟨869,by decide +kernel⟩ t)
def piece0972 : AffinePiece := pieces[870]'(by decide +kernel)
theorem intervalAccepted0972 : candidateIntervalCheck candidate0972 (227/500) (91/200) piece0972=true := by decide +kernel
noncomputable def cell0972 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0972 accepted0972 (227/500) (91/200) piece0972
    intervalAccepted0972 (fun t => piece_le_psi ⟨870,by decide +kernel⟩ t)
def piece0973 : AffinePiece := pieces[871]'(by decide +kernel)
theorem intervalAccepted0973 : candidateIntervalCheck candidate0973 (91/200) (57/125) piece0973=true := by decide +kernel
noncomputable def cell0973 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0973 accepted0973 (91/200) (57/125) piece0973
    intervalAccepted0973 (fun t => piece_le_psi ⟨871,by decide +kernel⟩ t)
def piece0974 : AffinePiece := pieces[872]'(by decide +kernel)
theorem intervalAccepted0974 : candidateIntervalCheck candidate0974 (57/125) (457/1000) piece0974=true := by decide +kernel
noncomputable def cell0974 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0974 accepted0974 (57/125) (457/1000) piece0974
    intervalAccepted0974 (fun t => piece_le_psi ⟨872,by decide +kernel⟩ t)
def piece0975 : AffinePiece := pieces[873]'(by decide +kernel)
theorem intervalAccepted0975 : candidateIntervalCheck candidate0975 (457/1000) (229/500) piece0975=true := by decide +kernel
noncomputable def cell0975 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0975 accepted0975 (457/1000) (229/500) piece0975
    intervalAccepted0975 (fun t => piece_le_psi ⟨873,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0960, cell0961, cell0962, cell0963, cell0964, cell0965, cell0966, cell0967, cell0968, cell0969, cell0970, cell0971, cell0972, cell0973, cell0974, cell0975]
theorem chainAccepted : spinCellChainCheck (221/500) (229/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (221/500) (229/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0060
