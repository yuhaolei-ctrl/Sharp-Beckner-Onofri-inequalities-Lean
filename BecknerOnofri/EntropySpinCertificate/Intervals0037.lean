module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0037

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0037
open CandidateBatch0037 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0592 : AffinePiece := pieces[552]'(by decide +kernel)
theorem intervalAccepted0592 : candidateIntervalCheck candidate0592 (1749/10000) (1751/10000) piece0592=true := by decide +kernel
noncomputable def cell0592 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0592 accepted0592 (1749/10000) (1751/10000) piece0592
    intervalAccepted0592 (fun t => piece_le_psi ⟨552,by decide +kernel⟩ t)
def piece0593 : AffinePiece := pieces[553]'(by decide +kernel)
theorem intervalAccepted0593 : candidateIntervalCheck candidate0593 (1751/10000) (1753/10000) piece0593=true := by decide +kernel
noncomputable def cell0593 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0593 accepted0593 (1751/10000) (1753/10000) piece0593
    intervalAccepted0593 (fun t => piece_le_psi ⟨553,by decide +kernel⟩ t)
def piece0594 : AffinePiece := pieces[554]'(by decide +kernel)
theorem intervalAccepted0594 : candidateIntervalCheck candidate0594 (1753/10000) (351/2000) piece0594=true := by decide +kernel
noncomputable def cell0594 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0594 accepted0594 (1753/10000) (351/2000) piece0594
    intervalAccepted0594 (fun t => piece_le_psi ⟨554,by decide +kernel⟩ t)
def piece0595 : AffinePiece := pieces[555]'(by decide +kernel)
theorem intervalAccepted0595 : candidateIntervalCheck candidate0595 (351/2000) (1757/10000) piece0595=true := by decide +kernel
noncomputable def cell0595 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0595 accepted0595 (351/2000) (1757/10000) piece0595
    intervalAccepted0595 (fun t => piece_le_psi ⟨555,by decide +kernel⟩ t)
def piece0596 : AffinePiece := pieces[556]'(by decide +kernel)
theorem intervalAccepted0596 : candidateIntervalCheck candidate0596 (1757/10000) (1759/10000) piece0596=true := by decide +kernel
noncomputable def cell0596 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0596 accepted0596 (1757/10000) (1759/10000) piece0596
    intervalAccepted0596 (fun t => piece_le_psi ⟨556,by decide +kernel⟩ t)
def piece0597 : AffinePiece := pieces[557]'(by decide +kernel)
theorem intervalAccepted0597 : candidateIntervalCheck candidate0597 (1759/10000) (1761/10000) piece0597=true := by decide +kernel
noncomputable def cell0597 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0597 accepted0597 (1759/10000) (1761/10000) piece0597
    intervalAccepted0597 (fun t => piece_le_psi ⟨557,by decide +kernel⟩ t)
def piece0598 : AffinePiece := pieces[558]'(by decide +kernel)
theorem intervalAccepted0598 : candidateIntervalCheck candidate0598 (1761/10000) (1763/10000) piece0598=true := by decide +kernel
noncomputable def cell0598 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0598 accepted0598 (1761/10000) (1763/10000) piece0598
    intervalAccepted0598 (fun t => piece_le_psi ⟨558,by decide +kernel⟩ t)
def piece0599 : AffinePiece := pieces[559]'(by decide +kernel)
theorem intervalAccepted0599 : candidateIntervalCheck candidate0599 (1763/10000) (353/2000) piece0599=true := by decide +kernel
noncomputable def cell0599 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0599 accepted0599 (1763/10000) (353/2000) piece0599
    intervalAccepted0599 (fun t => piece_le_psi ⟨559,by decide +kernel⟩ t)
def piece0600 : AffinePiece := pieces[560]'(by decide +kernel)
theorem intervalAccepted0600 : candidateIntervalCheck candidate0600 (353/2000) (1767/10000) piece0600=true := by decide +kernel
noncomputable def cell0600 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0600 accepted0600 (353/2000) (1767/10000) piece0600
    intervalAccepted0600 (fun t => piece_le_psi ⟨560,by decide +kernel⟩ t)
def piece0601 : AffinePiece := pieces[561]'(by decide +kernel)
theorem intervalAccepted0601 : candidateIntervalCheck candidate0601 (1767/10000) (1769/10000) piece0601=true := by decide +kernel
noncomputable def cell0601 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0601 accepted0601 (1767/10000) (1769/10000) piece0601
    intervalAccepted0601 (fun t => piece_le_psi ⟨561,by decide +kernel⟩ t)
def piece0602 : AffinePiece := pieces[562]'(by decide +kernel)
theorem intervalAccepted0602 : candidateIntervalCheck candidate0602 (1769/10000) (1771/10000) piece0602=true := by decide +kernel
noncomputable def cell0602 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0602 accepted0602 (1769/10000) (1771/10000) piece0602
    intervalAccepted0602 (fun t => piece_le_psi ⟨562,by decide +kernel⟩ t)
def piece0603 : AffinePiece := pieces[563]'(by decide +kernel)
theorem intervalAccepted0603 : candidateIntervalCheck candidate0603 (1771/10000) (1773/10000) piece0603=true := by decide +kernel
noncomputable def cell0603 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0603 accepted0603 (1771/10000) (1773/10000) piece0603
    intervalAccepted0603 (fun t => piece_le_psi ⟨563,by decide +kernel⟩ t)
def piece0604 : AffinePiece := pieces[564]'(by decide +kernel)
theorem intervalAccepted0604 : candidateIntervalCheck candidate0604 (1773/10000) (71/400) piece0604=true := by decide +kernel
noncomputable def cell0604 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0604 accepted0604 (1773/10000) (71/400) piece0604
    intervalAccepted0604 (fun t => piece_le_psi ⟨564,by decide +kernel⟩ t)
def piece0605 : AffinePiece := pieces[565]'(by decide +kernel)
theorem intervalAccepted0605 : candidateIntervalCheck candidate0605 (71/400) (1777/10000) piece0605=true := by decide +kernel
noncomputable def cell0605 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0605 accepted0605 (71/400) (1777/10000) piece0605
    intervalAccepted0605 (fun t => piece_le_psi ⟨565,by decide +kernel⟩ t)
def piece0606 : AffinePiece := pieces[566]'(by decide +kernel)
theorem intervalAccepted0606 : candidateIntervalCheck candidate0606 (1777/10000) (1779/10000) piece0606=true := by decide +kernel
noncomputable def cell0606 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0606 accepted0606 (1777/10000) (1779/10000) piece0606
    intervalAccepted0606 (fun t => piece_le_psi ⟨566,by decide +kernel⟩ t)
def piece0607 : AffinePiece := pieces[567]'(by decide +kernel)
theorem intervalAccepted0607 : candidateIntervalCheck candidate0607 (1779/10000) (1781/10000) piece0607=true := by decide +kernel
noncomputable def cell0607 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0607 accepted0607 (1779/10000) (1781/10000) piece0607
    intervalAccepted0607 (fun t => piece_le_psi ⟨567,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0592, cell0593, cell0594, cell0595, cell0596, cell0597, cell0598, cell0599, cell0600, cell0601, cell0602, cell0603, cell0604, cell0605, cell0606, cell0607]
theorem chainAccepted : spinCellChainCheck (1749/10000) (1781/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1749/10000) (1781/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0037
