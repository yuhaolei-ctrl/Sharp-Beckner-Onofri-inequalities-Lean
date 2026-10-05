module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0057

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0057
open CandidateBatch0057 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0912 : AffinePiece := pieces[810]'(by decide +kernel)
theorem intervalAccepted0912 : candidateIntervalCheck candidate0912 (197/500) (79/200) piece0912=true := by decide +kernel
noncomputable def cell0912 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0912 accepted0912 (197/500) (79/200) piece0912
    intervalAccepted0912 (fun t => piece_le_psi ⟨810,by decide +kernel⟩ t)
def piece0913 : AffinePiece := pieces[811]'(by decide +kernel)
theorem intervalAccepted0913 : candidateIntervalCheck candidate0913 (79/200) (99/250) piece0913=true := by decide +kernel
noncomputable def cell0913 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0913 accepted0913 (79/200) (99/250) piece0913
    intervalAccepted0913 (fun t => piece_le_psi ⟨811,by decide +kernel⟩ t)
def piece0914 : AffinePiece := pieces[812]'(by decide +kernel)
theorem intervalAccepted0914 : candidateIntervalCheck candidate0914 (99/250) (397/1000) piece0914=true := by decide +kernel
noncomputable def cell0914 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0914 accepted0914 (99/250) (397/1000) piece0914
    intervalAccepted0914 (fun t => piece_le_psi ⟨812,by decide +kernel⟩ t)
def piece0915 : AffinePiece := pieces[813]'(by decide +kernel)
theorem intervalAccepted0915 : candidateIntervalCheck candidate0915 (397/1000) (199/500) piece0915=true := by decide +kernel
noncomputable def cell0915 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0915 accepted0915 (397/1000) (199/500) piece0915
    intervalAccepted0915 (fun t => piece_le_psi ⟨813,by decide +kernel⟩ t)
def piece0916 : AffinePiece := pieces[814]'(by decide +kernel)
theorem intervalAccepted0916 : candidateIntervalCheck candidate0916 (199/500) (399/1000) piece0916=true := by decide +kernel
noncomputable def cell0916 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0916 accepted0916 (199/500) (399/1000) piece0916
    intervalAccepted0916 (fun t => piece_le_psi ⟨814,by decide +kernel⟩ t)
def piece0917 : AffinePiece := pieces[815]'(by decide +kernel)
theorem intervalAccepted0917 : candidateIntervalCheck candidate0917 (399/1000) (2/5) piece0917=true := by decide +kernel
noncomputable def cell0917 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0917 accepted0917 (399/1000) (2/5) piece0917
    intervalAccepted0917 (fun t => piece_le_psi ⟨815,by decide +kernel⟩ t)
def piece0918 : AffinePiece := pieces[816]'(by decide +kernel)
theorem intervalAccepted0918 : candidateIntervalCheck candidate0918 (2/5) (401/1000) piece0918=true := by decide +kernel
noncomputable def cell0918 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0918 accepted0918 (2/5) (401/1000) piece0918
    intervalAccepted0918 (fun t => piece_le_psi ⟨816,by decide +kernel⟩ t)
def piece0919 : AffinePiece := pieces[817]'(by decide +kernel)
theorem intervalAccepted0919 : candidateIntervalCheck candidate0919 (401/1000) (201/500) piece0919=true := by decide +kernel
noncomputable def cell0919 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0919 accepted0919 (401/1000) (201/500) piece0919
    intervalAccepted0919 (fun t => piece_le_psi ⟨817,by decide +kernel⟩ t)
def piece0920 : AffinePiece := pieces[818]'(by decide +kernel)
theorem intervalAccepted0920 : candidateIntervalCheck candidate0920 (201/500) (403/1000) piece0920=true := by decide +kernel
noncomputable def cell0920 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0920 accepted0920 (201/500) (403/1000) piece0920
    intervalAccepted0920 (fun t => piece_le_psi ⟨818,by decide +kernel⟩ t)
def piece0921 : AffinePiece := pieces[819]'(by decide +kernel)
theorem intervalAccepted0921 : candidateIntervalCheck candidate0921 (403/1000) (101/250) piece0921=true := by decide +kernel
noncomputable def cell0921 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0921 accepted0921 (403/1000) (101/250) piece0921
    intervalAccepted0921 (fun t => piece_le_psi ⟨819,by decide +kernel⟩ t)
def piece0922 : AffinePiece := pieces[820]'(by decide +kernel)
theorem intervalAccepted0922 : candidateIntervalCheck candidate0922 (101/250) (81/200) piece0922=true := by decide +kernel
noncomputable def cell0922 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0922 accepted0922 (101/250) (81/200) piece0922
    intervalAccepted0922 (fun t => piece_le_psi ⟨820,by decide +kernel⟩ t)
def piece0923 : AffinePiece := pieces[821]'(by decide +kernel)
theorem intervalAccepted0923 : candidateIntervalCheck candidate0923 (81/200) (203/500) piece0923=true := by decide +kernel
noncomputable def cell0923 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0923 accepted0923 (81/200) (203/500) piece0923
    intervalAccepted0923 (fun t => piece_le_psi ⟨821,by decide +kernel⟩ t)
def piece0924 : AffinePiece := pieces[822]'(by decide +kernel)
theorem intervalAccepted0924 : candidateIntervalCheck candidate0924 (203/500) (407/1000) piece0924=true := by decide +kernel
noncomputable def cell0924 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0924 accepted0924 (203/500) (407/1000) piece0924
    intervalAccepted0924 (fun t => piece_le_psi ⟨822,by decide +kernel⟩ t)
def piece0925 : AffinePiece := pieces[823]'(by decide +kernel)
theorem intervalAccepted0925 : candidateIntervalCheck candidate0925 (407/1000) (51/125) piece0925=true := by decide +kernel
noncomputable def cell0925 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0925 accepted0925 (407/1000) (51/125) piece0925
    intervalAccepted0925 (fun t => piece_le_psi ⟨823,by decide +kernel⟩ t)
def piece0926 : AffinePiece := pieces[824]'(by decide +kernel)
theorem intervalAccepted0926 : candidateIntervalCheck candidate0926 (51/125) (409/1000) piece0926=true := by decide +kernel
noncomputable def cell0926 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0926 accepted0926 (51/125) (409/1000) piece0926
    intervalAccepted0926 (fun t => piece_le_psi ⟨824,by decide +kernel⟩ t)
def piece0927 : AffinePiece := pieces[825]'(by decide +kernel)
theorem intervalAccepted0927 : candidateIntervalCheck candidate0927 (409/1000) (41/100) piece0927=true := by decide +kernel
noncomputable def cell0927 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0927 accepted0927 (409/1000) (41/100) piece0927
    intervalAccepted0927 (fun t => piece_le_psi ⟨825,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0912, cell0913, cell0914, cell0915, cell0916, cell0917, cell0918, cell0919, cell0920, cell0921, cell0922, cell0923, cell0924, cell0925, cell0926, cell0927]
theorem chainAccepted : spinCellChainCheck (197/500) (41/100) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (197/500) (41/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0057
