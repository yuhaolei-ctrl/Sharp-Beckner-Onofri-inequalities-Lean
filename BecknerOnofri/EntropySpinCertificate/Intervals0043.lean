import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0043
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0043
open CandidateBatch0043 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0688 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0688 : candidateIntervalCheck candidate0688 (1941/10000) (1943/10000) piece0688=true := by decide +kernel
noncomputable def cell0688 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0688 accepted0688 (1941/10000) (1943/10000) piece0688
    intervalAccepted0688 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0689 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0689 : candidateIntervalCheck candidate0689 (1943/10000) (389/2000) piece0689=true := by decide +kernel
noncomputable def cell0689 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0689 accepted0689 (1943/10000) (389/2000) piece0689
    intervalAccepted0689 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0690 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0690 : candidateIntervalCheck candidate0690 (389/2000) (1947/10000) piece0690=true := by decide +kernel
noncomputable def cell0690 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0690 accepted0690 (389/2000) (1947/10000) piece0690
    intervalAccepted0690 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0691 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0691 : candidateIntervalCheck candidate0691 (1947/10000) (1949/10000) piece0691=true := by decide +kernel
noncomputable def cell0691 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0691 accepted0691 (1947/10000) (1949/10000) piece0691
    intervalAccepted0691 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0692 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0692 : candidateIntervalCheck candidate0692 (1949/10000) (1951/10000) piece0692=true := by decide +kernel
noncomputable def cell0692 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0692 accepted0692 (1949/10000) (1951/10000) piece0692
    intervalAccepted0692 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0693 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0693 : candidateIntervalCheck candidate0693 (1951/10000) (1953/10000) piece0693=true := by decide +kernel
noncomputable def cell0693 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0693 accepted0693 (1951/10000) (1953/10000) piece0693
    intervalAccepted0693 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0694 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0694 : candidateIntervalCheck candidate0694 (1953/10000) (391/2000) piece0694=true := by decide +kernel
noncomputable def cell0694 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0694 accepted0694 (1953/10000) (391/2000) piece0694
    intervalAccepted0694 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0695 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0695 : candidateIntervalCheck candidate0695 (391/2000) (1957/10000) piece0695=true := by decide +kernel
noncomputable def cell0695 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0695 accepted0695 (391/2000) (1957/10000) piece0695
    intervalAccepted0695 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0696 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0696 : candidateIntervalCheck candidate0696 (1957/10000) (1959/10000) piece0696=true := by decide +kernel
noncomputable def cell0696 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0696 accepted0696 (1957/10000) (1959/10000) piece0696
    intervalAccepted0696 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0697 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0697 : candidateIntervalCheck candidate0697 (1959/10000) (1961/10000) piece0697=true := by decide +kernel
noncomputable def cell0697 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0697 accepted0697 (1959/10000) (1961/10000) piece0697
    intervalAccepted0697 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0698 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0698 : candidateIntervalCheck candidate0698 (1961/10000) (1963/10000) piece0698=true := by decide +kernel
noncomputable def cell0698 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0698 accepted0698 (1961/10000) (1963/10000) piece0698
    intervalAccepted0698 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0699 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0699 : candidateIntervalCheck candidate0699 (1963/10000) (393/2000) piece0699=true := by decide +kernel
noncomputable def cell0699 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0699 accepted0699 (1963/10000) (393/2000) piece0699
    intervalAccepted0699 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0700 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0700 : candidateIntervalCheck candidate0700 (393/2000) (1967/10000) piece0700=true := by decide +kernel
noncomputable def cell0700 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0700 accepted0700 (393/2000) (1967/10000) piece0700
    intervalAccepted0700 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0701 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0701 : candidateIntervalCheck candidate0701 (1967/10000) (1969/10000) piece0701=true := by decide +kernel
noncomputable def cell0701 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0701 accepted0701 (1967/10000) (1969/10000) piece0701
    intervalAccepted0701 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0702 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0702 : candidateIntervalCheck candidate0702 (1969/10000) (1971/10000) piece0702=true := by decide +kernel
noncomputable def cell0702 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0702 accepted0702 (1969/10000) (1971/10000) piece0702
    intervalAccepted0702 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0703 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0703 : candidateIntervalCheck candidate0703 (1971/10000) (1973/10000) piece0703=true := by decide +kernel
noncomputable def cell0703 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0703 accepted0703 (1971/10000) (1973/10000) piece0703
    intervalAccepted0703 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0688, cell0689, cell0690, cell0691, cell0692, cell0693, cell0694, cell0695, cell0696, cell0697, cell0698, cell0699, cell0700, cell0701, cell0702, cell0703]
theorem chainAccepted : spinCellChainCheck (1941/10000) (1973/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1941/10000) (1973/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0043
