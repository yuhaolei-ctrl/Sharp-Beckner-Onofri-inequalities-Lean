import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0039
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0039
open CandidateBatch0039 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0624 : AffinePiece := pieces[584]'(by decide +kernel)
theorem intervalAccepted0624 : candidateIntervalCheck candidate0624 (1813/10000) (363/2000) piece0624=true := by decide +kernel
noncomputable def cell0624 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0624 accepted0624 (1813/10000) (363/2000) piece0624
    intervalAccepted0624 (fun t => piece_le_psi ⟨584,by decide +kernel⟩ t)
def piece0625 : AffinePiece := pieces[585]'(by decide +kernel)
theorem intervalAccepted0625 : candidateIntervalCheck candidate0625 (363/2000) (1817/10000) piece0625=true := by decide +kernel
noncomputable def cell0625 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0625 accepted0625 (363/2000) (1817/10000) piece0625
    intervalAccepted0625 (fun t => piece_le_psi ⟨585,by decide +kernel⟩ t)
def piece0626 : AffinePiece := pieces[586]'(by decide +kernel)
theorem intervalAccepted0626 : candidateIntervalCheck candidate0626 (1817/10000) (1819/10000) piece0626=true := by decide +kernel
noncomputable def cell0626 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0626 accepted0626 (1817/10000) (1819/10000) piece0626
    intervalAccepted0626 (fun t => piece_le_psi ⟨586,by decide +kernel⟩ t)
def piece0627 : AffinePiece := pieces[587]'(by decide +kernel)
theorem intervalAccepted0627 : candidateIntervalCheck candidate0627 (1819/10000) (1821/10000) piece0627=true := by decide +kernel
noncomputable def cell0627 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0627 accepted0627 (1819/10000) (1821/10000) piece0627
    intervalAccepted0627 (fun t => piece_le_psi ⟨587,by decide +kernel⟩ t)
def piece0628 : AffinePiece := pieces[588]'(by decide +kernel)
theorem intervalAccepted0628 : candidateIntervalCheck candidate0628 (1821/10000) (1823/10000) piece0628=true := by decide +kernel
noncomputable def cell0628 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0628 accepted0628 (1821/10000) (1823/10000) piece0628
    intervalAccepted0628 (fun t => piece_le_psi ⟨588,by decide +kernel⟩ t)
def piece0629 : AffinePiece := pieces[589]'(by decide +kernel)
theorem intervalAccepted0629 : candidateIntervalCheck candidate0629 (1823/10000) (73/400) piece0629=true := by decide +kernel
noncomputable def cell0629 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0629 accepted0629 (1823/10000) (73/400) piece0629
    intervalAccepted0629 (fun t => piece_le_psi ⟨589,by decide +kernel⟩ t)
def piece0630 : AffinePiece := pieces[590]'(by decide +kernel)
theorem intervalAccepted0630 : candidateIntervalCheck candidate0630 (73/400) (1827/10000) piece0630=true := by decide +kernel
noncomputable def cell0630 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0630 accepted0630 (73/400) (1827/10000) piece0630
    intervalAccepted0630 (fun t => piece_le_psi ⟨590,by decide +kernel⟩ t)
def piece0631 : AffinePiece := pieces[591]'(by decide +kernel)
theorem intervalAccepted0631 : candidateIntervalCheck candidate0631 (1827/10000) (1829/10000) piece0631=true := by decide +kernel
noncomputable def cell0631 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0631 accepted0631 (1827/10000) (1829/10000) piece0631
    intervalAccepted0631 (fun t => piece_le_psi ⟨591,by decide +kernel⟩ t)
def piece0632 : AffinePiece := pieces[592]'(by decide +kernel)
theorem intervalAccepted0632 : candidateIntervalCheck candidate0632 (1829/10000) (1831/10000) piece0632=true := by decide +kernel
noncomputable def cell0632 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0632 accepted0632 (1829/10000) (1831/10000) piece0632
    intervalAccepted0632 (fun t => piece_le_psi ⟨592,by decide +kernel⟩ t)
def piece0633 : AffinePiece := pieces[593]'(by decide +kernel)
theorem intervalAccepted0633 : candidateIntervalCheck candidate0633 (1831/10000) (1833/10000) piece0633=true := by decide +kernel
noncomputable def cell0633 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0633 accepted0633 (1831/10000) (1833/10000) piece0633
    intervalAccepted0633 (fun t => piece_le_psi ⟨593,by decide +kernel⟩ t)
def piece0634 : AffinePiece := pieces[594]'(by decide +kernel)
theorem intervalAccepted0634 : candidateIntervalCheck candidate0634 (1833/10000) (367/2000) piece0634=true := by decide +kernel
noncomputable def cell0634 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0634 accepted0634 (1833/10000) (367/2000) piece0634
    intervalAccepted0634 (fun t => piece_le_psi ⟨594,by decide +kernel⟩ t)
def piece0635 : AffinePiece := pieces[595]'(by decide +kernel)
theorem intervalAccepted0635 : candidateIntervalCheck candidate0635 (367/2000) (1837/10000) piece0635=true := by decide +kernel
noncomputable def cell0635 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0635 accepted0635 (367/2000) (1837/10000) piece0635
    intervalAccepted0635 (fun t => piece_le_psi ⟨595,by decide +kernel⟩ t)
def piece0636 : AffinePiece := pieces[596]'(by decide +kernel)
theorem intervalAccepted0636 : candidateIntervalCheck candidate0636 (1837/10000) (1839/10000) piece0636=true := by decide +kernel
noncomputable def cell0636 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0636 accepted0636 (1837/10000) (1839/10000) piece0636
    intervalAccepted0636 (fun t => piece_le_psi ⟨596,by decide +kernel⟩ t)
def piece0637 : AffinePiece := pieces[597]'(by decide +kernel)
theorem intervalAccepted0637 : candidateIntervalCheck candidate0637 (1839/10000) (1841/10000) piece0637=true := by decide +kernel
noncomputable def cell0637 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0637 accepted0637 (1839/10000) (1841/10000) piece0637
    intervalAccepted0637 (fun t => piece_le_psi ⟨597,by decide +kernel⟩ t)
def piece0638 : AffinePiece := pieces[598]'(by decide +kernel)
theorem intervalAccepted0638 : candidateIntervalCheck candidate0638 (1841/10000) (1843/10000) piece0638=true := by decide +kernel
noncomputable def cell0638 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0638 accepted0638 (1841/10000) (1843/10000) piece0638
    intervalAccepted0638 (fun t => piece_le_psi ⟨598,by decide +kernel⟩ t)
def piece0639 : AffinePiece := pieces[599]'(by decide +kernel)
theorem intervalAccepted0639 : candidateIntervalCheck candidate0639 (1843/10000) (369/2000) piece0639=true := by decide +kernel
noncomputable def cell0639 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0639 accepted0639 (1843/10000) (369/2000) piece0639
    intervalAccepted0639 (fun t => piece_le_psi ⟨599,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0624, cell0625, cell0626, cell0627, cell0628, cell0629, cell0630, cell0631, cell0632, cell0633, cell0634, cell0635, cell0636, cell0637, cell0638, cell0639]
theorem chainAccepted : spinCellChainCheck (1813/10000) (369/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1813/10000) (369/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0039
