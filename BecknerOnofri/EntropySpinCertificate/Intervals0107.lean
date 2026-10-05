module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0107

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0107
open CandidateBatch0107 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1712 : AffinePiece := pieces[1470]'(by decide +kernel)
theorem intervalAccepted1712 : candidateIntervalCheck candidate1712 (4317/5000) (1727/2000) piece1712=true := by decide +kernel
noncomputable def cell1712 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1712 accepted1712 (4317/5000) (1727/2000) piece1712
    intervalAccepted1712 (fun t => piece_le_psi ⟨1470,by decide +kernel⟩ t)
def piece1713 : AffinePiece := pieces[1471]'(by decide +kernel)
theorem intervalAccepted1713 : candidateIntervalCheck candidate1713 (1727/2000) (2159/2500) piece1713=true := by decide +kernel
noncomputable def cell1713 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1713 accepted1713 (1727/2000) (2159/2500) piece1713
    intervalAccepted1713 (fun t => piece_le_psi ⟨1471,by decide +kernel⟩ t)
def piece1714 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1714 : candidateIntervalCheck candidate1714 (2159/2500) (8637/10000) piece1714=true := by decide +kernel
noncomputable def cell1714 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1714 accepted1714 (2159/2500) (8637/10000) piece1714
    intervalAccepted1714 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1715 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1715 : candidateIntervalCheck candidate1715 (8637/10000) (4319/5000) piece1715=true := by decide +kernel
noncomputable def cell1715 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1715 accepted1715 (8637/10000) (4319/5000) piece1715
    intervalAccepted1715 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1716 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1716 : candidateIntervalCheck candidate1716 (4319/5000) (8639/10000) piece1716=true := by decide +kernel
noncomputable def cell1716 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1716 accepted1716 (4319/5000) (8639/10000) piece1716
    intervalAccepted1716 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1717 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1717 : candidateIntervalCheck candidate1717 (8639/10000) (108/125) piece1717=true := by decide +kernel
noncomputable def cell1717 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1717 accepted1717 (8639/10000) (108/125) piece1717
    intervalAccepted1717 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1718 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1718 : candidateIntervalCheck candidate1718 (108/125) (8641/10000) piece1718=true := by decide +kernel
noncomputable def cell1718 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1718 accepted1718 (108/125) (8641/10000) piece1718
    intervalAccepted1718 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1719 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1719 : candidateIntervalCheck candidate1719 (8641/10000) (4321/5000) piece1719=true := by decide +kernel
noncomputable def cell1719 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1719 accepted1719 (8641/10000) (4321/5000) piece1719
    intervalAccepted1719 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1720 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1720 : candidateIntervalCheck candidate1720 (4321/5000) (8643/10000) piece1720=true := by decide +kernel
noncomputable def cell1720 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1720 accepted1720 (4321/5000) (8643/10000) piece1720
    intervalAccepted1720 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1721 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1721 : candidateIntervalCheck candidate1721 (8643/10000) (2161/2500) piece1721=true := by decide +kernel
noncomputable def cell1721 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1721 accepted1721 (8643/10000) (2161/2500) piece1721
    intervalAccepted1721 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1722 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1722 : candidateIntervalCheck candidate1722 (2161/2500) (1729/2000) piece1722=true := by decide +kernel
noncomputable def cell1722 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1722 accepted1722 (2161/2500) (1729/2000) piece1722
    intervalAccepted1722 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1723 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1723 : candidateIntervalCheck candidate1723 (1729/2000) (4323/5000) piece1723=true := by decide +kernel
noncomputable def cell1723 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1723 accepted1723 (1729/2000) (4323/5000) piece1723
    intervalAccepted1723 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1724 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1724 : candidateIntervalCheck candidate1724 (4323/5000) (8647/10000) piece1724=true := by decide +kernel
noncomputable def cell1724 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1724 accepted1724 (4323/5000) (8647/10000) piece1724
    intervalAccepted1724 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1725 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1725 : candidateIntervalCheck candidate1725 (8647/10000) (1081/1250) piece1725=true := by decide +kernel
noncomputable def cell1725 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1725 accepted1725 (8647/10000) (1081/1250) piece1725
    intervalAccepted1725 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1726 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1726 : candidateIntervalCheck candidate1726 (1081/1250) (8649/10000) piece1726=true := by decide +kernel
noncomputable def cell1726 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1726 accepted1726 (1081/1250) (8649/10000) piece1726
    intervalAccepted1726 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
def piece1727 : AffinePiece := pieces[1472]'(by decide +kernel)
theorem intervalAccepted1727 : candidateIntervalCheck candidate1727 (8649/10000) (173/200) piece1727=true := by decide +kernel
noncomputable def cell1727 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1727 accepted1727 (8649/10000) (173/200) piece1727
    intervalAccepted1727 (fun t => piece_le_psi ⟨1472,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1712, cell1713, cell1714, cell1715, cell1716, cell1717, cell1718, cell1719, cell1720, cell1721, cell1722, cell1723, cell1724, cell1725, cell1726, cell1727]
theorem chainAccepted : spinCellChainCheck (4317/5000) (173/200) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4317/5000) (173/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0107
