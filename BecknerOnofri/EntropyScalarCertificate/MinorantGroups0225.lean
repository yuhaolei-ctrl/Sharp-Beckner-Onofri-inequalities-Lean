module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0225

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0225
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1800 : minorantGammaCheck GammaPanel1800.certificate 1472=true := by decide +kernel
noncomputable def cell1800 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1800.certificate 1472 accepted1800
theorem accepted1801 : minorantGammaCheck GammaPanel1801.certificate 1472=true := by decide +kernel
noncomputable def cell1801 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1801.certificate 1472 accepted1801
theorem accepted1802 : minorantGammaCheck GammaPanel1802.certificate 1472=true := by decide +kernel
noncomputable def cell1802 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1802.certificate 1472 accepted1802
theorem accepted1803 : minorantGammaCheck GammaPanel1803.certificate 1472=true := by decide +kernel
noncomputable def cell1803 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1803.certificate 1472 accepted1803
theorem accepted1804 : minorantGammaCheck GammaPanel1804.certificate 1472=true := by decide +kernel
noncomputable def cell1804 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1804.certificate 1472 accepted1804
theorem accepted1805 : minorantGammaCheck GammaPanel1805.certificate 1472=true := by decide +kernel
noncomputable def cell1805 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1805.certificate 1472 accepted1805
theorem accepted1806 : minorantGammaCheck GammaPanel1806.certificate 1472=true := by decide +kernel
noncomputable def cell1806 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1806.certificate 1472 accepted1806
theorem accepted1807 : minorantGammaCheck GammaPanel1807.certificate 1472=true := by decide +kernel
noncomputable def cell1807 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1807.certificate 1472 accepted1807
noncomputable def cells : List CertifiedMinorantCell := [cell1800, cell1801, cell1802, cell1803, cell1804, cell1805, cell1806, cell1807]
theorem chainAccepted : minorantChainCheck (4361/5000) (873/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4361/5000) (873/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0225
