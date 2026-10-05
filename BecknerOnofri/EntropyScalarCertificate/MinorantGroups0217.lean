module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0217

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0217
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1736 : minorantGammaCheck GammaPanel1736.certificate 1472=true := by decide +kernel
noncomputable def cell1736 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1736.certificate 1472 accepted1736
theorem accepted1737 : minorantGammaCheck GammaPanel1737.certificate 1472=true := by decide +kernel
noncomputable def cell1737 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1737.certificate 1472 accepted1737
theorem accepted1738 : minorantGammaCheck GammaPanel1738.certificate 1472=true := by decide +kernel
noncomputable def cell1738 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1738.certificate 1472 accepted1738
theorem accepted1739 : minorantGammaCheck GammaPanel1739.certificate 1472=true := by decide +kernel
noncomputable def cell1739 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1739.certificate 1472 accepted1739
theorem accepted1740 : minorantGammaCheck GammaPanel1740.certificate 1472=true := by decide +kernel
noncomputable def cell1740 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1740.certificate 1472 accepted1740
theorem accepted1741 : minorantGammaCheck GammaPanel1741.certificate 1472=true := by decide +kernel
noncomputable def cell1741 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1741.certificate 1472 accepted1741
theorem accepted1742 : minorantGammaCheck GammaPanel1742.certificate 1472=true := by decide +kernel
noncomputable def cell1742 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1742.certificate 1472 accepted1742
theorem accepted1743 : minorantGammaCheck GammaPanel1743.certificate 1472=true := by decide +kernel
noncomputable def cell1743 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1743.certificate 1472 accepted1743
noncomputable def cells : List CertifiedMinorantCell := [cell1736, cell1737, cell1738, cell1739, cell1740, cell1741, cell1742, cell1743]
theorem chainAccepted : minorantChainCheck (4329/5000) (4333/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4329/5000) (4333/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0217
