module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0112

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0112
open CandidateBatch0112 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1792 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1792 : candidateIntervalCheck candidate1792 (4357/5000) (1743/2000) piece1792=true := by decide +kernel
noncomputable def cell1792 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1792 accepted1792 (4357/5000) (1743/2000) piece1792
    intervalAccepted1792 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1793 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1793 : candidateIntervalCheck candidate1793 (1743/2000) (2179/2500) piece1793=true := by decide +kernel
noncomputable def cell1793 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1793 accepted1793 (1743/2000) (2179/2500) piece1793
    intervalAccepted1793 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1794 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1794 : candidateIntervalCheck candidate1794 (2179/2500) (8717/10000) piece1794=true := by decide +kernel
noncomputable def cell1794 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1794 accepted1794 (2179/2500) (8717/10000) piece1794
    intervalAccepted1794 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1795 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1795 : candidateIntervalCheck candidate1795 (8717/10000) (4359/5000) piece1795=true := by decide +kernel
noncomputable def cell1795 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1795 accepted1795 (8717/10000) (4359/5000) piece1795
    intervalAccepted1795 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1796 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1796 : candidateIntervalCheck candidate1796 (4359/5000) (8719/10000) piece1796=true := by decide +kernel
noncomputable def cell1796 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1796 accepted1796 (4359/5000) (8719/10000) piece1796
    intervalAccepted1796 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1797 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1797 : candidateIntervalCheck candidate1797 (8719/10000) (109/125) piece1797=true := by decide +kernel
noncomputable def cell1797 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1797 accepted1797 (8719/10000) (109/125) piece1797
    intervalAccepted1797 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1798 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1798 : candidateIntervalCheck candidate1798 (109/125) (8721/10000) piece1798=true := by decide +kernel
noncomputable def cell1798 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1798 accepted1798 (109/125) (8721/10000) piece1798
    intervalAccepted1798 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1799 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1799 : candidateIntervalCheck candidate1799 (8721/10000) (4361/5000) piece1799=true := by decide +kernel
noncomputable def cell1799 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1799 accepted1799 (8721/10000) (4361/5000) piece1799
    intervalAccepted1799 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1800 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1800 : candidateIntervalCheck candidate1800 (4361/5000) (8723/10000) piece1800=true := by decide +kernel
noncomputable def cell1800 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1800 accepted1800 (4361/5000) (8723/10000) piece1800
    intervalAccepted1800 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1801 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1801 : candidateIntervalCheck candidate1801 (8723/10000) (2181/2500) piece1801=true := by decide +kernel
noncomputable def cell1801 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1801 accepted1801 (8723/10000) (2181/2500) piece1801
    intervalAccepted1801 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1802 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1802 : candidateIntervalCheck candidate1802 (2181/2500) (349/400) piece1802=true := by decide +kernel
noncomputable def cell1802 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1802 accepted1802 (2181/2500) (349/400) piece1802
    intervalAccepted1802 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1803 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1803 : candidateIntervalCheck candidate1803 (349/400) (4363/5000) piece1803=true := by decide +kernel
noncomputable def cell1803 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1803 accepted1803 (349/400) (4363/5000) piece1803
    intervalAccepted1803 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1804 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1804 : candidateIntervalCheck candidate1804 (4363/5000) (8727/10000) piece1804=true := by decide +kernel
noncomputable def cell1804 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1804 accepted1804 (4363/5000) (8727/10000) piece1804
    intervalAccepted1804 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1805 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1805 : candidateIntervalCheck candidate1805 (8727/10000) (1091/1250) piece1805=true := by decide +kernel
noncomputable def cell1805 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1805 accepted1805 (8727/10000) (1091/1250) piece1805
    intervalAccepted1805 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1806 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1806 : candidateIntervalCheck candidate1806 (1091/1250) (8729/10000) piece1806=true := by decide +kernel
noncomputable def cell1806 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1806 accepted1806 (1091/1250) (8729/10000) piece1806
    intervalAccepted1806 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1807 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1807 : candidateIntervalCheck candidate1807 (8729/10000) (873/1000) piece1807=true := by decide +kernel
noncomputable def cell1807 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1807 accepted1807 (8729/10000) (873/1000) piece1807
    intervalAccepted1807 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1792, cell1793, cell1794, cell1795, cell1796, cell1797, cell1798, cell1799, cell1800, cell1801, cell1802, cell1803, cell1804, cell1805, cell1806, cell1807]
theorem chainAccepted : spinCellChainCheck (4357/5000) (873/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4357/5000) (873/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0112
