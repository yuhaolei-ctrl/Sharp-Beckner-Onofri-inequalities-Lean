import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0040
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0040
open CandidateBatch0040 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0640 : AffinePiece := pieces[600]'(by decide +kernel)
theorem intervalAccepted0640 : candidateIntervalCheck candidate0640 (369/2000) (1847/10000) piece0640=true := by decide +kernel
noncomputable def cell0640 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0640 accepted0640 (369/2000) (1847/10000) piece0640
    intervalAccepted0640 (fun t => piece_le_psi ⟨600,by decide +kernel⟩ t)
def piece0641 : AffinePiece := pieces[601]'(by decide +kernel)
theorem intervalAccepted0641 : candidateIntervalCheck candidate0641 (1847/10000) (1849/10000) piece0641=true := by decide +kernel
noncomputable def cell0641 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0641 accepted0641 (1847/10000) (1849/10000) piece0641
    intervalAccepted0641 (fun t => piece_le_psi ⟨601,by decide +kernel⟩ t)
def piece0642 : AffinePiece := pieces[602]'(by decide +kernel)
theorem intervalAccepted0642 : candidateIntervalCheck candidate0642 (1849/10000) (1851/10000) piece0642=true := by decide +kernel
noncomputable def cell0642 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0642 accepted0642 (1849/10000) (1851/10000) piece0642
    intervalAccepted0642 (fun t => piece_le_psi ⟨602,by decide +kernel⟩ t)
def piece0643 : AffinePiece := pieces[603]'(by decide +kernel)
theorem intervalAccepted0643 : candidateIntervalCheck candidate0643 (1851/10000) (1853/10000) piece0643=true := by decide +kernel
noncomputable def cell0643 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0643 accepted0643 (1851/10000) (1853/10000) piece0643
    intervalAccepted0643 (fun t => piece_le_psi ⟨603,by decide +kernel⟩ t)
def piece0644 : AffinePiece := pieces[604]'(by decide +kernel)
theorem intervalAccepted0644 : candidateIntervalCheck candidate0644 (1853/10000) (371/2000) piece0644=true := by decide +kernel
noncomputable def cell0644 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0644 accepted0644 (1853/10000) (371/2000) piece0644
    intervalAccepted0644 (fun t => piece_le_psi ⟨604,by decide +kernel⟩ t)
def piece0645 : AffinePiece := pieces[605]'(by decide +kernel)
theorem intervalAccepted0645 : candidateIntervalCheck candidate0645 (371/2000) (1857/10000) piece0645=true := by decide +kernel
noncomputable def cell0645 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0645 accepted0645 (371/2000) (1857/10000) piece0645
    intervalAccepted0645 (fun t => piece_le_psi ⟨605,by decide +kernel⟩ t)
def piece0646 : AffinePiece := pieces[606]'(by decide +kernel)
theorem intervalAccepted0646 : candidateIntervalCheck candidate0646 (1857/10000) (1859/10000) piece0646=true := by decide +kernel
noncomputable def cell0646 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0646 accepted0646 (1857/10000) (1859/10000) piece0646
    intervalAccepted0646 (fun t => piece_le_psi ⟨606,by decide +kernel⟩ t)
def piece0647 : AffinePiece := pieces[607]'(by decide +kernel)
theorem intervalAccepted0647 : candidateIntervalCheck candidate0647 (1859/10000) (1861/10000) piece0647=true := by decide +kernel
noncomputable def cell0647 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0647 accepted0647 (1859/10000) (1861/10000) piece0647
    intervalAccepted0647 (fun t => piece_le_psi ⟨607,by decide +kernel⟩ t)
def piece0648 : AffinePiece := pieces[608]'(by decide +kernel)
theorem intervalAccepted0648 : candidateIntervalCheck candidate0648 (1861/10000) (1863/10000) piece0648=true := by decide +kernel
noncomputable def cell0648 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0648 accepted0648 (1861/10000) (1863/10000) piece0648
    intervalAccepted0648 (fun t => piece_le_psi ⟨608,by decide +kernel⟩ t)
def piece0649 : AffinePiece := pieces[609]'(by decide +kernel)
theorem intervalAccepted0649 : candidateIntervalCheck candidate0649 (1863/10000) (373/2000) piece0649=true := by decide +kernel
noncomputable def cell0649 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0649 accepted0649 (1863/10000) (373/2000) piece0649
    intervalAccepted0649 (fun t => piece_le_psi ⟨609,by decide +kernel⟩ t)
def piece0650 : AffinePiece := pieces[610]'(by decide +kernel)
theorem intervalAccepted0650 : candidateIntervalCheck candidate0650 (373/2000) (1867/10000) piece0650=true := by decide +kernel
noncomputable def cell0650 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0650 accepted0650 (373/2000) (1867/10000) piece0650
    intervalAccepted0650 (fun t => piece_le_psi ⟨610,by decide +kernel⟩ t)
def piece0651 : AffinePiece := pieces[611]'(by decide +kernel)
theorem intervalAccepted0651 : candidateIntervalCheck candidate0651 (1867/10000) (1869/10000) piece0651=true := by decide +kernel
noncomputable def cell0651 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0651 accepted0651 (1867/10000) (1869/10000) piece0651
    intervalAccepted0651 (fun t => piece_le_psi ⟨611,by decide +kernel⟩ t)
def piece0652 : AffinePiece := pieces[612]'(by decide +kernel)
theorem intervalAccepted0652 : candidateIntervalCheck candidate0652 (1869/10000) (1871/10000) piece0652=true := by decide +kernel
noncomputable def cell0652 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0652 accepted0652 (1869/10000) (1871/10000) piece0652
    intervalAccepted0652 (fun t => piece_le_psi ⟨612,by decide +kernel⟩ t)
def piece0653 : AffinePiece := pieces[613]'(by decide +kernel)
theorem intervalAccepted0653 : candidateIntervalCheck candidate0653 (1871/10000) (1873/10000) piece0653=true := by decide +kernel
noncomputable def cell0653 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0653 accepted0653 (1871/10000) (1873/10000) piece0653
    intervalAccepted0653 (fun t => piece_le_psi ⟨613,by decide +kernel⟩ t)
def piece0654 : AffinePiece := pieces[614]'(by decide +kernel)
theorem intervalAccepted0654 : candidateIntervalCheck candidate0654 (1873/10000) (3/16) piece0654=true := by decide +kernel
noncomputable def cell0654 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0654 accepted0654 (1873/10000) (3/16) piece0654
    intervalAccepted0654 (fun t => piece_le_psi ⟨614,by decide +kernel⟩ t)
def piece0655 : AffinePiece := pieces[615]'(by decide +kernel)
theorem intervalAccepted0655 : candidateIntervalCheck candidate0655 (3/16) (1877/10000) piece0655=true := by decide +kernel
noncomputable def cell0655 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0655 accepted0655 (3/16) (1877/10000) piece0655
    intervalAccepted0655 (fun t => piece_le_psi ⟨615,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0640, cell0641, cell0642, cell0643, cell0644, cell0645, cell0646, cell0647, cell0648, cell0649, cell0650, cell0651, cell0652, cell0653, cell0654, cell0655]
theorem chainAccepted : spinCellChainCheck (369/2000) (1877/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (369/2000) (1877/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0040
