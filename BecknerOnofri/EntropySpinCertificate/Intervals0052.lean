module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0052

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0052
open CandidateBatch0052 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0832 : AffinePiece := pieces[730]'(by decide +kernel)
theorem intervalAccepted0832 : candidateIntervalCheck candidate0832 (157/500) (63/200) piece0832=true := by decide +kernel
noncomputable def cell0832 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0832 accepted0832 (157/500) (63/200) piece0832
    intervalAccepted0832 (fun t => piece_le_psi ⟨730,by decide +kernel⟩ t)
def piece0833 : AffinePiece := pieces[731]'(by decide +kernel)
theorem intervalAccepted0833 : candidateIntervalCheck candidate0833 (63/200) (79/250) piece0833=true := by decide +kernel
noncomputable def cell0833 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0833 accepted0833 (63/200) (79/250) piece0833
    intervalAccepted0833 (fun t => piece_le_psi ⟨731,by decide +kernel⟩ t)
def piece0834 : AffinePiece := pieces[732]'(by decide +kernel)
theorem intervalAccepted0834 : candidateIntervalCheck candidate0834 (79/250) (317/1000) piece0834=true := by decide +kernel
noncomputable def cell0834 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0834 accepted0834 (79/250) (317/1000) piece0834
    intervalAccepted0834 (fun t => piece_le_psi ⟨732,by decide +kernel⟩ t)
def piece0835 : AffinePiece := pieces[733]'(by decide +kernel)
theorem intervalAccepted0835 : candidateIntervalCheck candidate0835 (317/1000) (159/500) piece0835=true := by decide +kernel
noncomputable def cell0835 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0835 accepted0835 (317/1000) (159/500) piece0835
    intervalAccepted0835 (fun t => piece_le_psi ⟨733,by decide +kernel⟩ t)
def piece0836 : AffinePiece := pieces[734]'(by decide +kernel)
theorem intervalAccepted0836 : candidateIntervalCheck candidate0836 (159/500) (319/1000) piece0836=true := by decide +kernel
noncomputable def cell0836 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0836 accepted0836 (159/500) (319/1000) piece0836
    intervalAccepted0836 (fun t => piece_le_psi ⟨734,by decide +kernel⟩ t)
def piece0837 : AffinePiece := pieces[735]'(by decide +kernel)
theorem intervalAccepted0837 : candidateIntervalCheck candidate0837 (319/1000) (8/25) piece0837=true := by decide +kernel
noncomputable def cell0837 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0837 accepted0837 (319/1000) (8/25) piece0837
    intervalAccepted0837 (fun t => piece_le_psi ⟨735,by decide +kernel⟩ t)
def piece0838 : AffinePiece := pieces[736]'(by decide +kernel)
theorem intervalAccepted0838 : candidateIntervalCheck candidate0838 (8/25) (321/1000) piece0838=true := by decide +kernel
noncomputable def cell0838 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0838 accepted0838 (8/25) (321/1000) piece0838
    intervalAccepted0838 (fun t => piece_le_psi ⟨736,by decide +kernel⟩ t)
def piece0839 : AffinePiece := pieces[737]'(by decide +kernel)
theorem intervalAccepted0839 : candidateIntervalCheck candidate0839 (321/1000) (161/500) piece0839=true := by decide +kernel
noncomputable def cell0839 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0839 accepted0839 (321/1000) (161/500) piece0839
    intervalAccepted0839 (fun t => piece_le_psi ⟨737,by decide +kernel⟩ t)
def piece0840 : AffinePiece := pieces[738]'(by decide +kernel)
theorem intervalAccepted0840 : candidateIntervalCheck candidate0840 (161/500) (323/1000) piece0840=true := by decide +kernel
noncomputable def cell0840 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0840 accepted0840 (161/500) (323/1000) piece0840
    intervalAccepted0840 (fun t => piece_le_psi ⟨738,by decide +kernel⟩ t)
def piece0841 : AffinePiece := pieces[739]'(by decide +kernel)
theorem intervalAccepted0841 : candidateIntervalCheck candidate0841 (323/1000) (81/250) piece0841=true := by decide +kernel
noncomputable def cell0841 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0841 accepted0841 (323/1000) (81/250) piece0841
    intervalAccepted0841 (fun t => piece_le_psi ⟨739,by decide +kernel⟩ t)
def piece0842 : AffinePiece := pieces[740]'(by decide +kernel)
theorem intervalAccepted0842 : candidateIntervalCheck candidate0842 (81/250) (13/40) piece0842=true := by decide +kernel
noncomputable def cell0842 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0842 accepted0842 (81/250) (13/40) piece0842
    intervalAccepted0842 (fun t => piece_le_psi ⟨740,by decide +kernel⟩ t)
def piece0843 : AffinePiece := pieces[741]'(by decide +kernel)
theorem intervalAccepted0843 : candidateIntervalCheck candidate0843 (13/40) (163/500) piece0843=true := by decide +kernel
noncomputable def cell0843 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0843 accepted0843 (13/40) (163/500) piece0843
    intervalAccepted0843 (fun t => piece_le_psi ⟨741,by decide +kernel⟩ t)
def piece0844 : AffinePiece := pieces[742]'(by decide +kernel)
theorem intervalAccepted0844 : candidateIntervalCheck candidate0844 (163/500) (327/1000) piece0844=true := by decide +kernel
noncomputable def cell0844 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0844 accepted0844 (163/500) (327/1000) piece0844
    intervalAccepted0844 (fun t => piece_le_psi ⟨742,by decide +kernel⟩ t)
def piece0845 : AffinePiece := pieces[743]'(by decide +kernel)
theorem intervalAccepted0845 : candidateIntervalCheck candidate0845 (327/1000) (41/125) piece0845=true := by decide +kernel
noncomputable def cell0845 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0845 accepted0845 (327/1000) (41/125) piece0845
    intervalAccepted0845 (fun t => piece_le_psi ⟨743,by decide +kernel⟩ t)
def piece0846 : AffinePiece := pieces[744]'(by decide +kernel)
theorem intervalAccepted0846 : candidateIntervalCheck candidate0846 (41/125) (329/1000) piece0846=true := by decide +kernel
noncomputable def cell0846 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0846 accepted0846 (41/125) (329/1000) piece0846
    intervalAccepted0846 (fun t => piece_le_psi ⟨744,by decide +kernel⟩ t)
def piece0847 : AffinePiece := pieces[745]'(by decide +kernel)
theorem intervalAccepted0847 : candidateIntervalCheck candidate0847 (329/1000) (33/100) piece0847=true := by decide +kernel
noncomputable def cell0847 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0847 accepted0847 (329/1000) (33/100) piece0847
    intervalAccepted0847 (fun t => piece_le_psi ⟨745,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0832, cell0833, cell0834, cell0835, cell0836, cell0837, cell0838, cell0839, cell0840, cell0841, cell0842, cell0843, cell0844, cell0845, cell0846, cell0847]
theorem chainAccepted : spinCellChainCheck (157/500) (33/100) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (157/500) (33/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0052
