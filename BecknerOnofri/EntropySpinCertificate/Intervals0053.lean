import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0053
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0053
open CandidateBatch0053 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0848 : AffinePiece := pieces[746]'(by decide +kernel)
theorem intervalAccepted0848 : candidateIntervalCheck candidate0848 (33/100) (331/1000) piece0848=true := by decide +kernel
noncomputable def cell0848 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0848 accepted0848 (33/100) (331/1000) piece0848
    intervalAccepted0848 (fun t => piece_le_psi ⟨746,by decide +kernel⟩ t)
def piece0849 : AffinePiece := pieces[747]'(by decide +kernel)
theorem intervalAccepted0849 : candidateIntervalCheck candidate0849 (331/1000) (83/250) piece0849=true := by decide +kernel
noncomputable def cell0849 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0849 accepted0849 (331/1000) (83/250) piece0849
    intervalAccepted0849 (fun t => piece_le_psi ⟨747,by decide +kernel⟩ t)
def piece0850 : AffinePiece := pieces[748]'(by decide +kernel)
theorem intervalAccepted0850 : candidateIntervalCheck candidate0850 (83/250) (333/1000) piece0850=true := by decide +kernel
noncomputable def cell0850 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0850 accepted0850 (83/250) (333/1000) piece0850
    intervalAccepted0850 (fun t => piece_le_psi ⟨748,by decide +kernel⟩ t)
def piece0851 : AffinePiece := pieces[749]'(by decide +kernel)
theorem intervalAccepted0851 : candidateIntervalCheck candidate0851 (333/1000) (167/500) piece0851=true := by decide +kernel
noncomputable def cell0851 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0851 accepted0851 (333/1000) (167/500) piece0851
    intervalAccepted0851 (fun t => piece_le_psi ⟨749,by decide +kernel⟩ t)
def piece0852 : AffinePiece := pieces[750]'(by decide +kernel)
theorem intervalAccepted0852 : candidateIntervalCheck candidate0852 (167/500) (67/200) piece0852=true := by decide +kernel
noncomputable def cell0852 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0852 accepted0852 (167/500) (67/200) piece0852
    intervalAccepted0852 (fun t => piece_le_psi ⟨750,by decide +kernel⟩ t)
def piece0853 : AffinePiece := pieces[751]'(by decide +kernel)
theorem intervalAccepted0853 : candidateIntervalCheck candidate0853 (67/200) (42/125) piece0853=true := by decide +kernel
noncomputable def cell0853 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0853 accepted0853 (67/200) (42/125) piece0853
    intervalAccepted0853 (fun t => piece_le_psi ⟨751,by decide +kernel⟩ t)
def piece0854 : AffinePiece := pieces[752]'(by decide +kernel)
theorem intervalAccepted0854 : candidateIntervalCheck candidate0854 (42/125) (337/1000) piece0854=true := by decide +kernel
noncomputable def cell0854 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0854 accepted0854 (42/125) (337/1000) piece0854
    intervalAccepted0854 (fun t => piece_le_psi ⟨752,by decide +kernel⟩ t)
def piece0855 : AffinePiece := pieces[753]'(by decide +kernel)
theorem intervalAccepted0855 : candidateIntervalCheck candidate0855 (337/1000) (169/500) piece0855=true := by decide +kernel
noncomputable def cell0855 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0855 accepted0855 (337/1000) (169/500) piece0855
    intervalAccepted0855 (fun t => piece_le_psi ⟨753,by decide +kernel⟩ t)
def piece0856 : AffinePiece := pieces[754]'(by decide +kernel)
theorem intervalAccepted0856 : candidateIntervalCheck candidate0856 (169/500) (339/1000) piece0856=true := by decide +kernel
noncomputable def cell0856 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0856 accepted0856 (169/500) (339/1000) piece0856
    intervalAccepted0856 (fun t => piece_le_psi ⟨754,by decide +kernel⟩ t)
def piece0857 : AffinePiece := pieces[755]'(by decide +kernel)
theorem intervalAccepted0857 : candidateIntervalCheck candidate0857 (339/1000) (17/50) piece0857=true := by decide +kernel
noncomputable def cell0857 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0857 accepted0857 (339/1000) (17/50) piece0857
    intervalAccepted0857 (fun t => piece_le_psi ⟨755,by decide +kernel⟩ t)
def piece0858 : AffinePiece := pieces[756]'(by decide +kernel)
theorem intervalAccepted0858 : candidateIntervalCheck candidate0858 (17/50) (341/1000) piece0858=true := by decide +kernel
noncomputable def cell0858 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0858 accepted0858 (17/50) (341/1000) piece0858
    intervalAccepted0858 (fun t => piece_le_psi ⟨756,by decide +kernel⟩ t)
def piece0859 : AffinePiece := pieces[757]'(by decide +kernel)
theorem intervalAccepted0859 : candidateIntervalCheck candidate0859 (341/1000) (171/500) piece0859=true := by decide +kernel
noncomputable def cell0859 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0859 accepted0859 (341/1000) (171/500) piece0859
    intervalAccepted0859 (fun t => piece_le_psi ⟨757,by decide +kernel⟩ t)
def piece0860 : AffinePiece := pieces[758]'(by decide +kernel)
theorem intervalAccepted0860 : candidateIntervalCheck candidate0860 (171/500) (343/1000) piece0860=true := by decide +kernel
noncomputable def cell0860 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0860 accepted0860 (171/500) (343/1000) piece0860
    intervalAccepted0860 (fun t => piece_le_psi ⟨758,by decide +kernel⟩ t)
def piece0861 : AffinePiece := pieces[759]'(by decide +kernel)
theorem intervalAccepted0861 : candidateIntervalCheck candidate0861 (343/1000) (43/125) piece0861=true := by decide +kernel
noncomputable def cell0861 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0861 accepted0861 (343/1000) (43/125) piece0861
    intervalAccepted0861 (fun t => piece_le_psi ⟨759,by decide +kernel⟩ t)
def piece0862 : AffinePiece := pieces[760]'(by decide +kernel)
theorem intervalAccepted0862 : candidateIntervalCheck candidate0862 (43/125) (69/200) piece0862=true := by decide +kernel
noncomputable def cell0862 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0862 accepted0862 (43/125) (69/200) piece0862
    intervalAccepted0862 (fun t => piece_le_psi ⟨760,by decide +kernel⟩ t)
def piece0863 : AffinePiece := pieces[761]'(by decide +kernel)
theorem intervalAccepted0863 : candidateIntervalCheck candidate0863 (69/200) (173/500) piece0863=true := by decide +kernel
noncomputable def cell0863 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0863 accepted0863 (69/200) (173/500) piece0863
    intervalAccepted0863 (fun t => piece_le_psi ⟨761,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0848, cell0849, cell0850, cell0851, cell0852, cell0853, cell0854, cell0855, cell0856, cell0857, cell0858, cell0859, cell0860, cell0861, cell0862, cell0863]
theorem chainAccepted : spinCellChainCheck (33/100) (173/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (33/100) (173/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0053
