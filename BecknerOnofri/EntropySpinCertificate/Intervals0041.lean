import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0041
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0041
open CandidateBatch0041 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0656 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0656 : candidateIntervalCheck candidate0656 (1877/10000) (1879/10000) piece0656=true := by decide +kernel
noncomputable def cell0656 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0656 accepted0656 (1877/10000) (1879/10000) piece0656
    intervalAccepted0656 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0657 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0657 : candidateIntervalCheck candidate0657 (1879/10000) (1881/10000) piece0657=true := by decide +kernel
noncomputable def cell0657 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0657 accepted0657 (1879/10000) (1881/10000) piece0657
    intervalAccepted0657 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0658 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0658 : candidateIntervalCheck candidate0658 (1881/10000) (1883/10000) piece0658=true := by decide +kernel
noncomputable def cell0658 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0658 accepted0658 (1881/10000) (1883/10000) piece0658
    intervalAccepted0658 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0659 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0659 : candidateIntervalCheck candidate0659 (1883/10000) (377/2000) piece0659=true := by decide +kernel
noncomputable def cell0659 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0659 accepted0659 (1883/10000) (377/2000) piece0659
    intervalAccepted0659 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0660 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0660 : candidateIntervalCheck candidate0660 (377/2000) (1887/10000) piece0660=true := by decide +kernel
noncomputable def cell0660 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0660 accepted0660 (377/2000) (1887/10000) piece0660
    intervalAccepted0660 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0661 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0661 : candidateIntervalCheck candidate0661 (1887/10000) (1889/10000) piece0661=true := by decide +kernel
noncomputable def cell0661 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0661 accepted0661 (1887/10000) (1889/10000) piece0661
    intervalAccepted0661 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0662 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0662 : candidateIntervalCheck candidate0662 (1889/10000) (1891/10000) piece0662=true := by decide +kernel
noncomputable def cell0662 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0662 accepted0662 (1889/10000) (1891/10000) piece0662
    intervalAccepted0662 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0663 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0663 : candidateIntervalCheck candidate0663 (1891/10000) (1893/10000) piece0663=true := by decide +kernel
noncomputable def cell0663 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0663 accepted0663 (1891/10000) (1893/10000) piece0663
    intervalAccepted0663 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0664 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0664 : candidateIntervalCheck candidate0664 (1893/10000) (379/2000) piece0664=true := by decide +kernel
noncomputable def cell0664 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0664 accepted0664 (1893/10000) (379/2000) piece0664
    intervalAccepted0664 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0665 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0665 : candidateIntervalCheck candidate0665 (379/2000) (1897/10000) piece0665=true := by decide +kernel
noncomputable def cell0665 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0665 accepted0665 (379/2000) (1897/10000) piece0665
    intervalAccepted0665 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0666 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0666 : candidateIntervalCheck candidate0666 (1897/10000) (1899/10000) piece0666=true := by decide +kernel
noncomputable def cell0666 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0666 accepted0666 (1897/10000) (1899/10000) piece0666
    intervalAccepted0666 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0667 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0667 : candidateIntervalCheck candidate0667 (1899/10000) (1901/10000) piece0667=true := by decide +kernel
noncomputable def cell0667 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0667 accepted0667 (1899/10000) (1901/10000) piece0667
    intervalAccepted0667 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0668 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0668 : candidateIntervalCheck candidate0668 (1901/10000) (1903/10000) piece0668=true := by decide +kernel
noncomputable def cell0668 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0668 accepted0668 (1901/10000) (1903/10000) piece0668
    intervalAccepted0668 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0669 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0669 : candidateIntervalCheck candidate0669 (1903/10000) (381/2000) piece0669=true := by decide +kernel
noncomputable def cell0669 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0669 accepted0669 (1903/10000) (381/2000) piece0669
    intervalAccepted0669 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0670 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0670 : candidateIntervalCheck candidate0670 (381/2000) (1907/10000) piece0670=true := by decide +kernel
noncomputable def cell0670 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0670 accepted0670 (381/2000) (1907/10000) piece0670
    intervalAccepted0670 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
def piece0671 : AffinePiece := pieces[616]'(by decide +kernel)
theorem intervalAccepted0671 : candidateIntervalCheck candidate0671 (1907/10000) (1909/10000) piece0671=true := by decide +kernel
noncomputable def cell0671 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0671 accepted0671 (1907/10000) (1909/10000) piece0671
    intervalAccepted0671 (fun t => piece_le_psi ⟨616,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0656, cell0657, cell0658, cell0659, cell0660, cell0661, cell0662, cell0663, cell0664, cell0665, cell0666, cell0667, cell0668, cell0669, cell0670, cell0671]
theorem chainAccepted : spinCellChainCheck (1877/10000) (1909/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1877/10000) (1909/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0041
