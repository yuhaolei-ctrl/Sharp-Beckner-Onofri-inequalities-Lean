module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0055

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0055
open CandidateBatch0055 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0880 : AffinePiece := pieces[778]'(by decide +kernel)
theorem intervalAccepted0880 : candidateIntervalCheck candidate0880 (181/500) (363/1000) piece0880=true := by decide +kernel
noncomputable def cell0880 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0880 accepted0880 (181/500) (363/1000) piece0880
    intervalAccepted0880 (fun t => piece_le_psi ⟨778,by decide +kernel⟩ t)
def piece0881 : AffinePiece := pieces[779]'(by decide +kernel)
theorem intervalAccepted0881 : candidateIntervalCheck candidate0881 (363/1000) (91/250) piece0881=true := by decide +kernel
noncomputable def cell0881 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0881 accepted0881 (363/1000) (91/250) piece0881
    intervalAccepted0881 (fun t => piece_le_psi ⟨779,by decide +kernel⟩ t)
def piece0882 : AffinePiece := pieces[780]'(by decide +kernel)
theorem intervalAccepted0882 : candidateIntervalCheck candidate0882 (91/250) (73/200) piece0882=true := by decide +kernel
noncomputable def cell0882 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0882 accepted0882 (91/250) (73/200) piece0882
    intervalAccepted0882 (fun t => piece_le_psi ⟨780,by decide +kernel⟩ t)
def piece0883 : AffinePiece := pieces[781]'(by decide +kernel)
theorem intervalAccepted0883 : candidateIntervalCheck candidate0883 (73/200) (183/500) piece0883=true := by decide +kernel
noncomputable def cell0883 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0883 accepted0883 (73/200) (183/500) piece0883
    intervalAccepted0883 (fun t => piece_le_psi ⟨781,by decide +kernel⟩ t)
def piece0884 : AffinePiece := pieces[782]'(by decide +kernel)
theorem intervalAccepted0884 : candidateIntervalCheck candidate0884 (183/500) (367/1000) piece0884=true := by decide +kernel
noncomputable def cell0884 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0884 accepted0884 (183/500) (367/1000) piece0884
    intervalAccepted0884 (fun t => piece_le_psi ⟨782,by decide +kernel⟩ t)
def piece0885 : AffinePiece := pieces[783]'(by decide +kernel)
theorem intervalAccepted0885 : candidateIntervalCheck candidate0885 (367/1000) (46/125) piece0885=true := by decide +kernel
noncomputable def cell0885 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0885 accepted0885 (367/1000) (46/125) piece0885
    intervalAccepted0885 (fun t => piece_le_psi ⟨783,by decide +kernel⟩ t)
def piece0886 : AffinePiece := pieces[784]'(by decide +kernel)
theorem intervalAccepted0886 : candidateIntervalCheck candidate0886 (46/125) (369/1000) piece0886=true := by decide +kernel
noncomputable def cell0886 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0886 accepted0886 (46/125) (369/1000) piece0886
    intervalAccepted0886 (fun t => piece_le_psi ⟨784,by decide +kernel⟩ t)
def piece0887 : AffinePiece := pieces[785]'(by decide +kernel)
theorem intervalAccepted0887 : candidateIntervalCheck candidate0887 (369/1000) (37/100) piece0887=true := by decide +kernel
noncomputable def cell0887 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0887 accepted0887 (369/1000) (37/100) piece0887
    intervalAccepted0887 (fun t => piece_le_psi ⟨785,by decide +kernel⟩ t)
def piece0888 : AffinePiece := pieces[786]'(by decide +kernel)
theorem intervalAccepted0888 : candidateIntervalCheck candidate0888 (37/100) (371/1000) piece0888=true := by decide +kernel
noncomputable def cell0888 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0888 accepted0888 (37/100) (371/1000) piece0888
    intervalAccepted0888 (fun t => piece_le_psi ⟨786,by decide +kernel⟩ t)
def piece0889 : AffinePiece := pieces[787]'(by decide +kernel)
theorem intervalAccepted0889 : candidateIntervalCheck candidate0889 (371/1000) (93/250) piece0889=true := by decide +kernel
noncomputable def cell0889 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0889 accepted0889 (371/1000) (93/250) piece0889
    intervalAccepted0889 (fun t => piece_le_psi ⟨787,by decide +kernel⟩ t)
def piece0890 : AffinePiece := pieces[788]'(by decide +kernel)
theorem intervalAccepted0890 : candidateIntervalCheck candidate0890 (93/250) (373/1000) piece0890=true := by decide +kernel
noncomputable def cell0890 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0890 accepted0890 (93/250) (373/1000) piece0890
    intervalAccepted0890 (fun t => piece_le_psi ⟨788,by decide +kernel⟩ t)
def piece0891 : AffinePiece := pieces[789]'(by decide +kernel)
theorem intervalAccepted0891 : candidateIntervalCheck candidate0891 (373/1000) (187/500) piece0891=true := by decide +kernel
noncomputable def cell0891 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0891 accepted0891 (373/1000) (187/500) piece0891
    intervalAccepted0891 (fun t => piece_le_psi ⟨789,by decide +kernel⟩ t)
def piece0892 : AffinePiece := pieces[790]'(by decide +kernel)
theorem intervalAccepted0892 : candidateIntervalCheck candidate0892 (187/500) (3/8) piece0892=true := by decide +kernel
noncomputable def cell0892 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0892 accepted0892 (187/500) (3/8) piece0892
    intervalAccepted0892 (fun t => piece_le_psi ⟨790,by decide +kernel⟩ t)
def piece0893 : AffinePiece := pieces[791]'(by decide +kernel)
theorem intervalAccepted0893 : candidateIntervalCheck candidate0893 (3/8) (47/125) piece0893=true := by decide +kernel
noncomputable def cell0893 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0893 accepted0893 (3/8) (47/125) piece0893
    intervalAccepted0893 (fun t => piece_le_psi ⟨791,by decide +kernel⟩ t)
def piece0894 : AffinePiece := pieces[792]'(by decide +kernel)
theorem intervalAccepted0894 : candidateIntervalCheck candidate0894 (47/125) (377/1000) piece0894=true := by decide +kernel
noncomputable def cell0894 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0894 accepted0894 (47/125) (377/1000) piece0894
    intervalAccepted0894 (fun t => piece_le_psi ⟨792,by decide +kernel⟩ t)
def piece0895 : AffinePiece := pieces[793]'(by decide +kernel)
theorem intervalAccepted0895 : candidateIntervalCheck candidate0895 (377/1000) (189/500) piece0895=true := by decide +kernel
noncomputable def cell0895 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0895 accepted0895 (377/1000) (189/500) piece0895
    intervalAccepted0895 (fun t => piece_le_psi ⟨793,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0880, cell0881, cell0882, cell0883, cell0884, cell0885, cell0886, cell0887, cell0888, cell0889, cell0890, cell0891, cell0892, cell0893, cell0894, cell0895]
theorem chainAccepted : spinCellChainCheck (181/500) (189/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (181/500) (189/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0055
