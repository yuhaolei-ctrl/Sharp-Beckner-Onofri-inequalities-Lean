import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0056
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0056
open CandidateBatch0056 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0896 : AffinePiece := pieces[794]'(by decide +kernel)
theorem intervalAccepted0896 : candidateIntervalCheck candidate0896 (189/500) (379/1000) piece0896=true := by decide +kernel
noncomputable def cell0896 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0896 accepted0896 (189/500) (379/1000) piece0896
    intervalAccepted0896 (fun t => piece_le_psi ⟨794,by decide +kernel⟩ t)
def piece0897 : AffinePiece := pieces[795]'(by decide +kernel)
theorem intervalAccepted0897 : candidateIntervalCheck candidate0897 (379/1000) (19/50) piece0897=true := by decide +kernel
noncomputable def cell0897 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0897 accepted0897 (379/1000) (19/50) piece0897
    intervalAccepted0897 (fun t => piece_le_psi ⟨795,by decide +kernel⟩ t)
def piece0898 : AffinePiece := pieces[796]'(by decide +kernel)
theorem intervalAccepted0898 : candidateIntervalCheck candidate0898 (19/50) (381/1000) piece0898=true := by decide +kernel
noncomputable def cell0898 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0898 accepted0898 (19/50) (381/1000) piece0898
    intervalAccepted0898 (fun t => piece_le_psi ⟨796,by decide +kernel⟩ t)
def piece0899 : AffinePiece := pieces[797]'(by decide +kernel)
theorem intervalAccepted0899 : candidateIntervalCheck candidate0899 (381/1000) (191/500) piece0899=true := by decide +kernel
noncomputable def cell0899 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0899 accepted0899 (381/1000) (191/500) piece0899
    intervalAccepted0899 (fun t => piece_le_psi ⟨797,by decide +kernel⟩ t)
def piece0900 : AffinePiece := pieces[798]'(by decide +kernel)
theorem intervalAccepted0900 : candidateIntervalCheck candidate0900 (191/500) (383/1000) piece0900=true := by decide +kernel
noncomputable def cell0900 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0900 accepted0900 (191/500) (383/1000) piece0900
    intervalAccepted0900 (fun t => piece_le_psi ⟨798,by decide +kernel⟩ t)
def piece0901 : AffinePiece := pieces[799]'(by decide +kernel)
theorem intervalAccepted0901 : candidateIntervalCheck candidate0901 (383/1000) (48/125) piece0901=true := by decide +kernel
noncomputable def cell0901 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0901 accepted0901 (383/1000) (48/125) piece0901
    intervalAccepted0901 (fun t => piece_le_psi ⟨799,by decide +kernel⟩ t)
def piece0902 : AffinePiece := pieces[800]'(by decide +kernel)
theorem intervalAccepted0902 : candidateIntervalCheck candidate0902 (48/125) (77/200) piece0902=true := by decide +kernel
noncomputable def cell0902 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0902 accepted0902 (48/125) (77/200) piece0902
    intervalAccepted0902 (fun t => piece_le_psi ⟨800,by decide +kernel⟩ t)
def piece0903 : AffinePiece := pieces[801]'(by decide +kernel)
theorem intervalAccepted0903 : candidateIntervalCheck candidate0903 (77/200) (193/500) piece0903=true := by decide +kernel
noncomputable def cell0903 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0903 accepted0903 (77/200) (193/500) piece0903
    intervalAccepted0903 (fun t => piece_le_psi ⟨801,by decide +kernel⟩ t)
def piece0904 : AffinePiece := pieces[802]'(by decide +kernel)
theorem intervalAccepted0904 : candidateIntervalCheck candidate0904 (193/500) (387/1000) piece0904=true := by decide +kernel
noncomputable def cell0904 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0904 accepted0904 (193/500) (387/1000) piece0904
    intervalAccepted0904 (fun t => piece_le_psi ⟨802,by decide +kernel⟩ t)
def piece0905 : AffinePiece := pieces[803]'(by decide +kernel)
theorem intervalAccepted0905 : candidateIntervalCheck candidate0905 (387/1000) (97/250) piece0905=true := by decide +kernel
noncomputable def cell0905 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0905 accepted0905 (387/1000) (97/250) piece0905
    intervalAccepted0905 (fun t => piece_le_psi ⟨803,by decide +kernel⟩ t)
def piece0906 : AffinePiece := pieces[804]'(by decide +kernel)
theorem intervalAccepted0906 : candidateIntervalCheck candidate0906 (97/250) (389/1000) piece0906=true := by decide +kernel
noncomputable def cell0906 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0906 accepted0906 (97/250) (389/1000) piece0906
    intervalAccepted0906 (fun t => piece_le_psi ⟨804,by decide +kernel⟩ t)
def piece0907 : AffinePiece := pieces[805]'(by decide +kernel)
theorem intervalAccepted0907 : candidateIntervalCheck candidate0907 (389/1000) (39/100) piece0907=true := by decide +kernel
noncomputable def cell0907 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0907 accepted0907 (389/1000) (39/100) piece0907
    intervalAccepted0907 (fun t => piece_le_psi ⟨805,by decide +kernel⟩ t)
def piece0908 : AffinePiece := pieces[806]'(by decide +kernel)
theorem intervalAccepted0908 : candidateIntervalCheck candidate0908 (39/100) (391/1000) piece0908=true := by decide +kernel
noncomputable def cell0908 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0908 accepted0908 (39/100) (391/1000) piece0908
    intervalAccepted0908 (fun t => piece_le_psi ⟨806,by decide +kernel⟩ t)
def piece0909 : AffinePiece := pieces[807]'(by decide +kernel)
theorem intervalAccepted0909 : candidateIntervalCheck candidate0909 (391/1000) (49/125) piece0909=true := by decide +kernel
noncomputable def cell0909 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0909 accepted0909 (391/1000) (49/125) piece0909
    intervalAccepted0909 (fun t => piece_le_psi ⟨807,by decide +kernel⟩ t)
def piece0910 : AffinePiece := pieces[808]'(by decide +kernel)
theorem intervalAccepted0910 : candidateIntervalCheck candidate0910 (49/125) (393/1000) piece0910=true := by decide +kernel
noncomputable def cell0910 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0910 accepted0910 (49/125) (393/1000) piece0910
    intervalAccepted0910 (fun t => piece_le_psi ⟨808,by decide +kernel⟩ t)
def piece0911 : AffinePiece := pieces[809]'(by decide +kernel)
theorem intervalAccepted0911 : candidateIntervalCheck candidate0911 (393/1000) (197/500) piece0911=true := by decide +kernel
noncomputable def cell0911 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0911 accepted0911 (393/1000) (197/500) piece0911
    intervalAccepted0911 (fun t => piece_le_psi ⟨809,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0896, cell0897, cell0898, cell0899, cell0900, cell0901, cell0902, cell0903, cell0904, cell0905, cell0906, cell0907, cell0908, cell0909, cell0910, cell0911]
theorem chainAccepted : spinCellChainCheck (189/500) (197/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (189/500) (197/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0056
