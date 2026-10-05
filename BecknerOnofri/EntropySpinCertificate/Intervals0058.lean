import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0058
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0058
open CandidateBatch0058 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0928 : AffinePiece := pieces[826]'(by decide +kernel)
theorem intervalAccepted0928 : candidateIntervalCheck candidate0928 (41/100) (411/1000) piece0928=true := by decide +kernel
noncomputable def cell0928 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0928 accepted0928 (41/100) (411/1000) piece0928
    intervalAccepted0928 (fun t => piece_le_psi ⟨826,by decide +kernel⟩ t)
def piece0929 : AffinePiece := pieces[827]'(by decide +kernel)
theorem intervalAccepted0929 : candidateIntervalCheck candidate0929 (411/1000) (103/250) piece0929=true := by decide +kernel
noncomputable def cell0929 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0929 accepted0929 (411/1000) (103/250) piece0929
    intervalAccepted0929 (fun t => piece_le_psi ⟨827,by decide +kernel⟩ t)
def piece0930 : AffinePiece := pieces[828]'(by decide +kernel)
theorem intervalAccepted0930 : candidateIntervalCheck candidate0930 (103/250) (413/1000) piece0930=true := by decide +kernel
noncomputable def cell0930 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0930 accepted0930 (103/250) (413/1000) piece0930
    intervalAccepted0930 (fun t => piece_le_psi ⟨828,by decide +kernel⟩ t)
def piece0931 : AffinePiece := pieces[829]'(by decide +kernel)
theorem intervalAccepted0931 : candidateIntervalCheck candidate0931 (413/1000) (207/500) piece0931=true := by decide +kernel
noncomputable def cell0931 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0931 accepted0931 (413/1000) (207/500) piece0931
    intervalAccepted0931 (fun t => piece_le_psi ⟨829,by decide +kernel⟩ t)
def piece0932 : AffinePiece := pieces[830]'(by decide +kernel)
theorem intervalAccepted0932 : candidateIntervalCheck candidate0932 (207/500) (83/200) piece0932=true := by decide +kernel
noncomputable def cell0932 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0932 accepted0932 (207/500) (83/200) piece0932
    intervalAccepted0932 (fun t => piece_le_psi ⟨830,by decide +kernel⟩ t)
def piece0933 : AffinePiece := pieces[831]'(by decide +kernel)
theorem intervalAccepted0933 : candidateIntervalCheck candidate0933 (83/200) (52/125) piece0933=true := by decide +kernel
noncomputable def cell0933 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0933 accepted0933 (83/200) (52/125) piece0933
    intervalAccepted0933 (fun t => piece_le_psi ⟨831,by decide +kernel⟩ t)
def piece0934 : AffinePiece := pieces[832]'(by decide +kernel)
theorem intervalAccepted0934 : candidateIntervalCheck candidate0934 (52/125) (417/1000) piece0934=true := by decide +kernel
noncomputable def cell0934 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0934 accepted0934 (52/125) (417/1000) piece0934
    intervalAccepted0934 (fun t => piece_le_psi ⟨832,by decide +kernel⟩ t)
def piece0935 : AffinePiece := pieces[833]'(by decide +kernel)
theorem intervalAccepted0935 : candidateIntervalCheck candidate0935 (417/1000) (209/500) piece0935=true := by decide +kernel
noncomputable def cell0935 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0935 accepted0935 (417/1000) (209/500) piece0935
    intervalAccepted0935 (fun t => piece_le_psi ⟨833,by decide +kernel⟩ t)
def piece0936 : AffinePiece := pieces[834]'(by decide +kernel)
theorem intervalAccepted0936 : candidateIntervalCheck candidate0936 (209/500) (419/1000) piece0936=true := by decide +kernel
noncomputable def cell0936 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0936 accepted0936 (209/500) (419/1000) piece0936
    intervalAccepted0936 (fun t => piece_le_psi ⟨834,by decide +kernel⟩ t)
def piece0937 : AffinePiece := pieces[835]'(by decide +kernel)
theorem intervalAccepted0937 : candidateIntervalCheck candidate0937 (419/1000) (21/50) piece0937=true := by decide +kernel
noncomputable def cell0937 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0937 accepted0937 (419/1000) (21/50) piece0937
    intervalAccepted0937 (fun t => piece_le_psi ⟨835,by decide +kernel⟩ t)
def piece0938 : AffinePiece := pieces[836]'(by decide +kernel)
theorem intervalAccepted0938 : candidateIntervalCheck candidate0938 (21/50) (421/1000) piece0938=true := by decide +kernel
noncomputable def cell0938 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0938 accepted0938 (21/50) (421/1000) piece0938
    intervalAccepted0938 (fun t => piece_le_psi ⟨836,by decide +kernel⟩ t)
def piece0939 : AffinePiece := pieces[837]'(by decide +kernel)
theorem intervalAccepted0939 : candidateIntervalCheck candidate0939 (421/1000) (211/500) piece0939=true := by decide +kernel
noncomputable def cell0939 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0939 accepted0939 (421/1000) (211/500) piece0939
    intervalAccepted0939 (fun t => piece_le_psi ⟨837,by decide +kernel⟩ t)
def piece0940 : AffinePiece := pieces[838]'(by decide +kernel)
theorem intervalAccepted0940 : candidateIntervalCheck candidate0940 (211/500) (423/1000) piece0940=true := by decide +kernel
noncomputable def cell0940 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0940 accepted0940 (211/500) (423/1000) piece0940
    intervalAccepted0940 (fun t => piece_le_psi ⟨838,by decide +kernel⟩ t)
def piece0941 : AffinePiece := pieces[839]'(by decide +kernel)
theorem intervalAccepted0941 : candidateIntervalCheck candidate0941 (423/1000) (53/125) piece0941=true := by decide +kernel
noncomputable def cell0941 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0941 accepted0941 (423/1000) (53/125) piece0941
    intervalAccepted0941 (fun t => piece_le_psi ⟨839,by decide +kernel⟩ t)
def piece0942 : AffinePiece := pieces[840]'(by decide +kernel)
theorem intervalAccepted0942 : candidateIntervalCheck candidate0942 (53/125) (17/40) piece0942=true := by decide +kernel
noncomputable def cell0942 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0942 accepted0942 (53/125) (17/40) piece0942
    intervalAccepted0942 (fun t => piece_le_psi ⟨840,by decide +kernel⟩ t)
def piece0943 : AffinePiece := pieces[841]'(by decide +kernel)
theorem intervalAccepted0943 : candidateIntervalCheck candidate0943 (17/40) (213/500) piece0943=true := by decide +kernel
noncomputable def cell0943 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0943 accepted0943 (17/40) (213/500) piece0943
    intervalAccepted0943 (fun t => piece_le_psi ⟨841,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0928, cell0929, cell0930, cell0931, cell0932, cell0933, cell0934, cell0935, cell0936, cell0937, cell0938, cell0939, cell0940, cell0941, cell0942, cell0943]
theorem chainAccepted : spinCellChainCheck (41/100) (213/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (41/100) (213/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0058
