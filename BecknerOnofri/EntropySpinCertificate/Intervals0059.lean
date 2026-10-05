module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0059

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0059
open CandidateBatch0059 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0944 : AffinePiece := pieces[842]'(by decide +kernel)
theorem intervalAccepted0944 : candidateIntervalCheck candidate0944 (213/500) (427/1000) piece0944=true := by decide +kernel
noncomputable def cell0944 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0944 accepted0944 (213/500) (427/1000) piece0944
    intervalAccepted0944 (fun t => piece_le_psi ⟨842,by decide +kernel⟩ t)
def piece0945 : AffinePiece := pieces[843]'(by decide +kernel)
theorem intervalAccepted0945 : candidateIntervalCheck candidate0945 (427/1000) (107/250) piece0945=true := by decide +kernel
noncomputable def cell0945 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0945 accepted0945 (427/1000) (107/250) piece0945
    intervalAccepted0945 (fun t => piece_le_psi ⟨843,by decide +kernel⟩ t)
def piece0946 : AffinePiece := pieces[844]'(by decide +kernel)
theorem intervalAccepted0946 : candidateIntervalCheck candidate0946 (107/250) (429/1000) piece0946=true := by decide +kernel
noncomputable def cell0946 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0946 accepted0946 (107/250) (429/1000) piece0946
    intervalAccepted0946 (fun t => piece_le_psi ⟨844,by decide +kernel⟩ t)
def piece0947 : AffinePiece := pieces[845]'(by decide +kernel)
theorem intervalAccepted0947 : candidateIntervalCheck candidate0947 (429/1000) (43/100) piece0947=true := by decide +kernel
noncomputable def cell0947 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0947 accepted0947 (429/1000) (43/100) piece0947
    intervalAccepted0947 (fun t => piece_le_psi ⟨845,by decide +kernel⟩ t)
def piece0948 : AffinePiece := pieces[846]'(by decide +kernel)
theorem intervalAccepted0948 : candidateIntervalCheck candidate0948 (43/100) (431/1000) piece0948=true := by decide +kernel
noncomputable def cell0948 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0948 accepted0948 (43/100) (431/1000) piece0948
    intervalAccepted0948 (fun t => piece_le_psi ⟨846,by decide +kernel⟩ t)
def piece0949 : AffinePiece := pieces[847]'(by decide +kernel)
theorem intervalAccepted0949 : candidateIntervalCheck candidate0949 (431/1000) (54/125) piece0949=true := by decide +kernel
noncomputable def cell0949 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0949 accepted0949 (431/1000) (54/125) piece0949
    intervalAccepted0949 (fun t => piece_le_psi ⟨847,by decide +kernel⟩ t)
def piece0950 : AffinePiece := pieces[848]'(by decide +kernel)
theorem intervalAccepted0950 : candidateIntervalCheck candidate0950 (54/125) (433/1000) piece0950=true := by decide +kernel
noncomputable def cell0950 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0950 accepted0950 (54/125) (433/1000) piece0950
    intervalAccepted0950 (fun t => piece_le_psi ⟨848,by decide +kernel⟩ t)
def piece0951 : AffinePiece := pieces[849]'(by decide +kernel)
theorem intervalAccepted0951 : candidateIntervalCheck candidate0951 (433/1000) (217/500) piece0951=true := by decide +kernel
noncomputable def cell0951 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0951 accepted0951 (433/1000) (217/500) piece0951
    intervalAccepted0951 (fun t => piece_le_psi ⟨849,by decide +kernel⟩ t)
def piece0952 : AffinePiece := pieces[850]'(by decide +kernel)
theorem intervalAccepted0952 : candidateIntervalCheck candidate0952 (217/500) (87/200) piece0952=true := by decide +kernel
noncomputable def cell0952 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0952 accepted0952 (217/500) (87/200) piece0952
    intervalAccepted0952 (fun t => piece_le_psi ⟨850,by decide +kernel⟩ t)
def piece0953 : AffinePiece := pieces[851]'(by decide +kernel)
theorem intervalAccepted0953 : candidateIntervalCheck candidate0953 (87/200) (109/250) piece0953=true := by decide +kernel
noncomputable def cell0953 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0953 accepted0953 (87/200) (109/250) piece0953
    intervalAccepted0953 (fun t => piece_le_psi ⟨851,by decide +kernel⟩ t)
def piece0954 : AffinePiece := pieces[852]'(by decide +kernel)
theorem intervalAccepted0954 : candidateIntervalCheck candidate0954 (109/250) (437/1000) piece0954=true := by decide +kernel
noncomputable def cell0954 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0954 accepted0954 (109/250) (437/1000) piece0954
    intervalAccepted0954 (fun t => piece_le_psi ⟨852,by decide +kernel⟩ t)
def piece0955 : AffinePiece := pieces[853]'(by decide +kernel)
theorem intervalAccepted0955 : candidateIntervalCheck candidate0955 (437/1000) (219/500) piece0955=true := by decide +kernel
noncomputable def cell0955 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0955 accepted0955 (437/1000) (219/500) piece0955
    intervalAccepted0955 (fun t => piece_le_psi ⟨853,by decide +kernel⟩ t)
def piece0956 : AffinePiece := pieces[854]'(by decide +kernel)
theorem intervalAccepted0956 : candidateIntervalCheck candidate0956 (219/500) (439/1000) piece0956=true := by decide +kernel
noncomputable def cell0956 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0956 accepted0956 (219/500) (439/1000) piece0956
    intervalAccepted0956 (fun t => piece_le_psi ⟨854,by decide +kernel⟩ t)
def piece0957 : AffinePiece := pieces[855]'(by decide +kernel)
theorem intervalAccepted0957 : candidateIntervalCheck candidate0957 (439/1000) (11/25) piece0957=true := by decide +kernel
noncomputable def cell0957 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0957 accepted0957 (439/1000) (11/25) piece0957
    intervalAccepted0957 (fun t => piece_le_psi ⟨855,by decide +kernel⟩ t)
def piece0958 : AffinePiece := pieces[856]'(by decide +kernel)
theorem intervalAccepted0958 : candidateIntervalCheck candidate0958 (11/25) (441/1000) piece0958=true := by decide +kernel
noncomputable def cell0958 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0958 accepted0958 (11/25) (441/1000) piece0958
    intervalAccepted0958 (fun t => piece_le_psi ⟨856,by decide +kernel⟩ t)
def piece0959 : AffinePiece := pieces[857]'(by decide +kernel)
theorem intervalAccepted0959 : candidateIntervalCheck candidate0959 (441/1000) (221/500) piece0959=true := by decide +kernel
noncomputable def cell0959 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0959 accepted0959 (441/1000) (221/500) piece0959
    intervalAccepted0959 (fun t => piece_le_psi ⟨857,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0944, cell0945, cell0946, cell0947, cell0948, cell0949, cell0950, cell0951, cell0952, cell0953, cell0954, cell0955, cell0956, cell0957, cell0958, cell0959]
theorem chainAccepted : spinCellChainCheck (213/500) (221/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (213/500) (221/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0059
