import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0054
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0054
open CandidateBatch0054 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0864 : AffinePiece := pieces[762]'(by decide +kernel)
theorem intervalAccepted0864 : candidateIntervalCheck candidate0864 (173/500) (347/1000) piece0864=true := by decide +kernel
noncomputable def cell0864 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0864 accepted0864 (173/500) (347/1000) piece0864
    intervalAccepted0864 (fun t => piece_le_psi ⟨762,by decide +kernel⟩ t)
def piece0865 : AffinePiece := pieces[763]'(by decide +kernel)
theorem intervalAccepted0865 : candidateIntervalCheck candidate0865 (347/1000) (87/250) piece0865=true := by decide +kernel
noncomputable def cell0865 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0865 accepted0865 (347/1000) (87/250) piece0865
    intervalAccepted0865 (fun t => piece_le_psi ⟨763,by decide +kernel⟩ t)
def piece0866 : AffinePiece := pieces[764]'(by decide +kernel)
theorem intervalAccepted0866 : candidateIntervalCheck candidate0866 (87/250) (349/1000) piece0866=true := by decide +kernel
noncomputable def cell0866 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0866 accepted0866 (87/250) (349/1000) piece0866
    intervalAccepted0866 (fun t => piece_le_psi ⟨764,by decide +kernel⟩ t)
def piece0867 : AffinePiece := pieces[765]'(by decide +kernel)
theorem intervalAccepted0867 : candidateIntervalCheck candidate0867 (349/1000) (7/20) piece0867=true := by decide +kernel
noncomputable def cell0867 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0867 accepted0867 (349/1000) (7/20) piece0867
    intervalAccepted0867 (fun t => piece_le_psi ⟨765,by decide +kernel⟩ t)
def piece0868 : AffinePiece := pieces[766]'(by decide +kernel)
theorem intervalAccepted0868 : candidateIntervalCheck candidate0868 (7/20) (351/1000) piece0868=true := by decide +kernel
noncomputable def cell0868 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0868 accepted0868 (7/20) (351/1000) piece0868
    intervalAccepted0868 (fun t => piece_le_psi ⟨766,by decide +kernel⟩ t)
def piece0869 : AffinePiece := pieces[767]'(by decide +kernel)
theorem intervalAccepted0869 : candidateIntervalCheck candidate0869 (351/1000) (44/125) piece0869=true := by decide +kernel
noncomputable def cell0869 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0869 accepted0869 (351/1000) (44/125) piece0869
    intervalAccepted0869 (fun t => piece_le_psi ⟨767,by decide +kernel⟩ t)
def piece0870 : AffinePiece := pieces[768]'(by decide +kernel)
theorem intervalAccepted0870 : candidateIntervalCheck candidate0870 (44/125) (353/1000) piece0870=true := by decide +kernel
noncomputable def cell0870 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0870 accepted0870 (44/125) (353/1000) piece0870
    intervalAccepted0870 (fun t => piece_le_psi ⟨768,by decide +kernel⟩ t)
def piece0871 : AffinePiece := pieces[769]'(by decide +kernel)
theorem intervalAccepted0871 : candidateIntervalCheck candidate0871 (353/1000) (177/500) piece0871=true := by decide +kernel
noncomputable def cell0871 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0871 accepted0871 (353/1000) (177/500) piece0871
    intervalAccepted0871 (fun t => piece_le_psi ⟨769,by decide +kernel⟩ t)
def piece0872 : AffinePiece := pieces[770]'(by decide +kernel)
theorem intervalAccepted0872 : candidateIntervalCheck candidate0872 (177/500) (71/200) piece0872=true := by decide +kernel
noncomputable def cell0872 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0872 accepted0872 (177/500) (71/200) piece0872
    intervalAccepted0872 (fun t => piece_le_psi ⟨770,by decide +kernel⟩ t)
def piece0873 : AffinePiece := pieces[771]'(by decide +kernel)
theorem intervalAccepted0873 : candidateIntervalCheck candidate0873 (71/200) (89/250) piece0873=true := by decide +kernel
noncomputable def cell0873 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0873 accepted0873 (71/200) (89/250) piece0873
    intervalAccepted0873 (fun t => piece_le_psi ⟨771,by decide +kernel⟩ t)
def piece0874 : AffinePiece := pieces[772]'(by decide +kernel)
theorem intervalAccepted0874 : candidateIntervalCheck candidate0874 (89/250) (357/1000) piece0874=true := by decide +kernel
noncomputable def cell0874 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0874 accepted0874 (89/250) (357/1000) piece0874
    intervalAccepted0874 (fun t => piece_le_psi ⟨772,by decide +kernel⟩ t)
def piece0875 : AffinePiece := pieces[773]'(by decide +kernel)
theorem intervalAccepted0875 : candidateIntervalCheck candidate0875 (357/1000) (179/500) piece0875=true := by decide +kernel
noncomputable def cell0875 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0875 accepted0875 (357/1000) (179/500) piece0875
    intervalAccepted0875 (fun t => piece_le_psi ⟨773,by decide +kernel⟩ t)
def piece0876 : AffinePiece := pieces[774]'(by decide +kernel)
theorem intervalAccepted0876 : candidateIntervalCheck candidate0876 (179/500) (359/1000) piece0876=true := by decide +kernel
noncomputable def cell0876 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0876 accepted0876 (179/500) (359/1000) piece0876
    intervalAccepted0876 (fun t => piece_le_psi ⟨774,by decide +kernel⟩ t)
def piece0877 : AffinePiece := pieces[775]'(by decide +kernel)
theorem intervalAccepted0877 : candidateIntervalCheck candidate0877 (359/1000) (9/25) piece0877=true := by decide +kernel
noncomputable def cell0877 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0877 accepted0877 (359/1000) (9/25) piece0877
    intervalAccepted0877 (fun t => piece_le_psi ⟨775,by decide +kernel⟩ t)
def piece0878 : AffinePiece := pieces[776]'(by decide +kernel)
theorem intervalAccepted0878 : candidateIntervalCheck candidate0878 (9/25) (361/1000) piece0878=true := by decide +kernel
noncomputable def cell0878 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0878 accepted0878 (9/25) (361/1000) piece0878
    intervalAccepted0878 (fun t => piece_le_psi ⟨776,by decide +kernel⟩ t)
def piece0879 : AffinePiece := pieces[777]'(by decide +kernel)
theorem intervalAccepted0879 : candidateIntervalCheck candidate0879 (361/1000) (181/500) piece0879=true := by decide +kernel
noncomputable def cell0879 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0879 accepted0879 (361/1000) (181/500) piece0879
    intervalAccepted0879 (fun t => piece_le_psi ⟨777,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0864, cell0865, cell0866, cell0867, cell0868, cell0869, cell0870, cell0871, cell0872, cell0873, cell0874, cell0875, cell0876, cell0877, cell0878, cell0879]
theorem chainAccepted : spinCellChainCheck (173/500) (181/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (173/500) (181/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0054
