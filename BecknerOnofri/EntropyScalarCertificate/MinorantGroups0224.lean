module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0224

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0224
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1792 : minorantGammaCheck GammaPanel1792.certificate 1472=true := by decide +kernel
noncomputable def cell1792 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1792.certificate 1472 accepted1792
theorem accepted1793 : minorantGammaCheck GammaPanel1793.certificate 1472=true := by decide +kernel
noncomputable def cell1793 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1793.certificate 1472 accepted1793
theorem accepted1794 : minorantGammaCheck GammaPanel1794.certificate 1472=true := by decide +kernel
noncomputable def cell1794 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1794.certificate 1472 accepted1794
theorem accepted1795 : minorantGammaCheck GammaPanel1795.certificate 1472=true := by decide +kernel
noncomputable def cell1795 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1795.certificate 1472 accepted1795
theorem accepted1796 : minorantGammaCheck GammaPanel1796.certificate 1472=true := by decide +kernel
noncomputable def cell1796 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1796.certificate 1472 accepted1796
theorem accepted1797 : minorantGammaCheck GammaPanel1797.certificate 1472=true := by decide +kernel
noncomputable def cell1797 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1797.certificate 1472 accepted1797
theorem accepted1798 : minorantGammaCheck GammaPanel1798.certificate 1472=true := by decide +kernel
noncomputable def cell1798 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1798.certificate 1472 accepted1798
theorem accepted1799 : minorantGammaCheck GammaPanel1799.certificate 1472=true := by decide +kernel
noncomputable def cell1799 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1799.certificate 1472 accepted1799
noncomputable def cells : List CertifiedMinorantCell := [cell1792, cell1793, cell1794, cell1795, cell1796, cell1797, cell1798, cell1799]
theorem chainAccepted : minorantChainCheck (4357/5000) (4361/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4357/5000) (4361/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0224
