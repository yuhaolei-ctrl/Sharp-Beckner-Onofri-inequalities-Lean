import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0061
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0061
open CandidateBatch0061 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0976 : AffinePiece := pieces[874]'(by decide +kernel)
theorem intervalAccepted0976 : candidateIntervalCheck candidate0976 (229/500) (459/1000) piece0976=true := by decide +kernel
noncomputable def cell0976 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0976 accepted0976 (229/500) (459/1000) piece0976
    intervalAccepted0976 (fun t => piece_le_psi ⟨874,by decide +kernel⟩ t)
def piece0977 : AffinePiece := pieces[875]'(by decide +kernel)
theorem intervalAccepted0977 : candidateIntervalCheck candidate0977 (459/1000) (23/50) piece0977=true := by decide +kernel
noncomputable def cell0977 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0977 accepted0977 (459/1000) (23/50) piece0977
    intervalAccepted0977 (fun t => piece_le_psi ⟨875,by decide +kernel⟩ t)
def piece0978 : AffinePiece := pieces[876]'(by decide +kernel)
theorem intervalAccepted0978 : candidateIntervalCheck candidate0978 (23/50) (461/1000) piece0978=true := by decide +kernel
noncomputable def cell0978 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0978 accepted0978 (23/50) (461/1000) piece0978
    intervalAccepted0978 (fun t => piece_le_psi ⟨876,by decide +kernel⟩ t)
def piece0979 : AffinePiece := pieces[877]'(by decide +kernel)
theorem intervalAccepted0979 : candidateIntervalCheck candidate0979 (461/1000) (231/500) piece0979=true := by decide +kernel
noncomputable def cell0979 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0979 accepted0979 (461/1000) (231/500) piece0979
    intervalAccepted0979 (fun t => piece_le_psi ⟨877,by decide +kernel⟩ t)
def piece0980 : AffinePiece := pieces[878]'(by decide +kernel)
theorem intervalAccepted0980 : candidateIntervalCheck candidate0980 (231/500) (463/1000) piece0980=true := by decide +kernel
noncomputable def cell0980 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0980 accepted0980 (231/500) (463/1000) piece0980
    intervalAccepted0980 (fun t => piece_le_psi ⟨878,by decide +kernel⟩ t)
def piece0981 : AffinePiece := pieces[879]'(by decide +kernel)
theorem intervalAccepted0981 : candidateIntervalCheck candidate0981 (463/1000) (58/125) piece0981=true := by decide +kernel
noncomputable def cell0981 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0981 accepted0981 (463/1000) (58/125) piece0981
    intervalAccepted0981 (fun t => piece_le_psi ⟨879,by decide +kernel⟩ t)
def piece0982 : AffinePiece := pieces[880]'(by decide +kernel)
theorem intervalAccepted0982 : candidateIntervalCheck candidate0982 (58/125) (93/200) piece0982=true := by decide +kernel
noncomputable def cell0982 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0982 accepted0982 (58/125) (93/200) piece0982
    intervalAccepted0982 (fun t => piece_le_psi ⟨880,by decide +kernel⟩ t)
def piece0983 : AffinePiece := pieces[881]'(by decide +kernel)
theorem intervalAccepted0983 : candidateIntervalCheck candidate0983 (93/200) (233/500) piece0983=true := by decide +kernel
noncomputable def cell0983 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0983 accepted0983 (93/200) (233/500) piece0983
    intervalAccepted0983 (fun t => piece_le_psi ⟨881,by decide +kernel⟩ t)
def piece0984 : AffinePiece := pieces[882]'(by decide +kernel)
theorem intervalAccepted0984 : candidateIntervalCheck candidate0984 (233/500) (467/1000) piece0984=true := by decide +kernel
noncomputable def cell0984 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0984 accepted0984 (233/500) (467/1000) piece0984
    intervalAccepted0984 (fun t => piece_le_psi ⟨882,by decide +kernel⟩ t)
def piece0985 : AffinePiece := pieces[883]'(by decide +kernel)
theorem intervalAccepted0985 : candidateIntervalCheck candidate0985 (467/1000) (117/250) piece0985=true := by decide +kernel
noncomputable def cell0985 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0985 accepted0985 (467/1000) (117/250) piece0985
    intervalAccepted0985 (fun t => piece_le_psi ⟨883,by decide +kernel⟩ t)
def piece0986 : AffinePiece := pieces[884]'(by decide +kernel)
theorem intervalAccepted0986 : candidateIntervalCheck candidate0986 (117/250) (469/1000) piece0986=true := by decide +kernel
noncomputable def cell0986 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0986 accepted0986 (117/250) (469/1000) piece0986
    intervalAccepted0986 (fun t => piece_le_psi ⟨884,by decide +kernel⟩ t)
def piece0987 : AffinePiece := pieces[885]'(by decide +kernel)
theorem intervalAccepted0987 : candidateIntervalCheck candidate0987 (469/1000) (47/100) piece0987=true := by decide +kernel
noncomputable def cell0987 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0987 accepted0987 (469/1000) (47/100) piece0987
    intervalAccepted0987 (fun t => piece_le_psi ⟨885,by decide +kernel⟩ t)
def piece0988 : AffinePiece := pieces[886]'(by decide +kernel)
theorem intervalAccepted0988 : candidateIntervalCheck candidate0988 (47/100) (471/1000) piece0988=true := by decide +kernel
noncomputable def cell0988 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0988 accepted0988 (47/100) (471/1000) piece0988
    intervalAccepted0988 (fun t => piece_le_psi ⟨886,by decide +kernel⟩ t)
def piece0989 : AffinePiece := pieces[887]'(by decide +kernel)
theorem intervalAccepted0989 : candidateIntervalCheck candidate0989 (471/1000) (59/125) piece0989=true := by decide +kernel
noncomputable def cell0989 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0989 accepted0989 (471/1000) (59/125) piece0989
    intervalAccepted0989 (fun t => piece_le_psi ⟨887,by decide +kernel⟩ t)
def piece0990 : AffinePiece := pieces[888]'(by decide +kernel)
theorem intervalAccepted0990 : candidateIntervalCheck candidate0990 (59/125) (473/1000) piece0990=true := by decide +kernel
noncomputable def cell0990 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0990 accepted0990 (59/125) (473/1000) piece0990
    intervalAccepted0990 (fun t => piece_le_psi ⟨888,by decide +kernel⟩ t)
def piece0991 : AffinePiece := pieces[889]'(by decide +kernel)
theorem intervalAccepted0991 : candidateIntervalCheck candidate0991 (473/1000) (237/500) piece0991=true := by decide +kernel
noncomputable def cell0991 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0991 accepted0991 (473/1000) (237/500) piece0991
    intervalAccepted0991 (fun t => piece_le_psi ⟨889,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0976, cell0977, cell0978, cell0979, cell0980, cell0981, cell0982, cell0983, cell0984, cell0985, cell0986, cell0987, cell0988, cell0989, cell0990, cell0991]
theorem chainAccepted : spinCellChainCheck (229/500) (237/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (229/500) (237/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0061
