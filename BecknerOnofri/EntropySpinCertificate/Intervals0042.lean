module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0042

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0042
open CandidateBatch0042 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0672 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0672 : candidateIntervalCheck candidate0672 (1909/10000) (1911/10000) piece0672=true := by decide +kernel
noncomputable def cell0672 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0672 accepted0672 (1909/10000) (1911/10000) piece0672
    intervalAccepted0672 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0673 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0673 : candidateIntervalCheck candidate0673 (1911/10000) (1913/10000) piece0673=true := by decide +kernel
noncomputable def cell0673 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0673 accepted0673 (1911/10000) (1913/10000) piece0673
    intervalAccepted0673 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0674 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0674 : candidateIntervalCheck candidate0674 (1913/10000) (383/2000) piece0674=true := by decide +kernel
noncomputable def cell0674 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0674 accepted0674 (1913/10000) (383/2000) piece0674
    intervalAccepted0674 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0675 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0675 : candidateIntervalCheck candidate0675 (383/2000) (1917/10000) piece0675=true := by decide +kernel
noncomputable def cell0675 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0675 accepted0675 (383/2000) (1917/10000) piece0675
    intervalAccepted0675 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0676 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0676 : candidateIntervalCheck candidate0676 (1917/10000) (1919/10000) piece0676=true := by decide +kernel
noncomputable def cell0676 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0676 accepted0676 (1917/10000) (1919/10000) piece0676
    intervalAccepted0676 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0677 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0677 : candidateIntervalCheck candidate0677 (1919/10000) (1921/10000) piece0677=true := by decide +kernel
noncomputable def cell0677 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0677 accepted0677 (1919/10000) (1921/10000) piece0677
    intervalAccepted0677 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0678 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0678 : candidateIntervalCheck candidate0678 (1921/10000) (1923/10000) piece0678=true := by decide +kernel
noncomputable def cell0678 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0678 accepted0678 (1921/10000) (1923/10000) piece0678
    intervalAccepted0678 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0679 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0679 : candidateIntervalCheck candidate0679 (1923/10000) (77/400) piece0679=true := by decide +kernel
noncomputable def cell0679 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0679 accepted0679 (1923/10000) (77/400) piece0679
    intervalAccepted0679 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0680 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0680 : candidateIntervalCheck candidate0680 (77/400) (1927/10000) piece0680=true := by decide +kernel
noncomputable def cell0680 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0680 accepted0680 (77/400) (1927/10000) piece0680
    intervalAccepted0680 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0681 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0681 : candidateIntervalCheck candidate0681 (1927/10000) (1929/10000) piece0681=true := by decide +kernel
noncomputable def cell0681 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0681 accepted0681 (1927/10000) (1929/10000) piece0681
    intervalAccepted0681 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0682 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0682 : candidateIntervalCheck candidate0682 (1929/10000) (1931/10000) piece0682=true := by decide +kernel
noncomputable def cell0682 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0682 accepted0682 (1929/10000) (1931/10000) piece0682
    intervalAccepted0682 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0683 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0683 : candidateIntervalCheck candidate0683 (1931/10000) (1933/10000) piece0683=true := by decide +kernel
noncomputable def cell0683 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0683 accepted0683 (1931/10000) (1933/10000) piece0683
    intervalAccepted0683 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0684 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0684 : candidateIntervalCheck candidate0684 (1933/10000) (387/2000) piece0684=true := by decide +kernel
noncomputable def cell0684 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0684 accepted0684 (1933/10000) (387/2000) piece0684
    intervalAccepted0684 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0685 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0685 : candidateIntervalCheck candidate0685 (387/2000) (1937/10000) piece0685=true := by decide +kernel
noncomputable def cell0685 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0685 accepted0685 (387/2000) (1937/10000) piece0685
    intervalAccepted0685 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0686 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0686 : candidateIntervalCheck candidate0686 (1937/10000) (1939/10000) piece0686=true := by decide +kernel
noncomputable def cell0686 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0686 accepted0686 (1937/10000) (1939/10000) piece0686
    intervalAccepted0686 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0687 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0687 : candidateIntervalCheck candidate0687 (1939/10000) (1941/10000) piece0687=true := by decide +kernel
noncomputable def cell0687 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0687 accepted0687 (1939/10000) (1941/10000) piece0687
    intervalAccepted0687 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0672, cell0673, cell0674, cell0675, cell0676, cell0677, cell0678, cell0679, cell0680, cell0681, cell0682, cell0683, cell0684, cell0685, cell0686, cell0687]
theorem chainAccepted : spinCellChainCheck (1909/10000) (1941/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1909/10000) (1941/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0042
