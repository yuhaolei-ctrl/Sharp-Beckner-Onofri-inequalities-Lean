module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0226

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0226
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1808 : minorantGammaCheck GammaPanel1808.certificate 1472=true := by decide +kernel
noncomputable def cell1808 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1808.certificate 1472 accepted1808
theorem accepted1809 : minorantGammaCheck GammaPanel1809.certificate 1472=true := by decide +kernel
noncomputable def cell1809 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1809.certificate 1472 accepted1809
theorem accepted1810 : minorantGammaCheck GammaPanel1810.certificate 1472=true := by decide +kernel
noncomputable def cell1810 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1810.certificate 1472 accepted1810
theorem accepted1811 : minorantGammaCheck GammaPanel1811.certificate 1472=true := by decide +kernel
noncomputable def cell1811 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1811.certificate 1472 accepted1811
theorem accepted1812 : minorantGammaCheck GammaPanel1812.certificate 1472=true := by decide +kernel
noncomputable def cell1812 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1812.certificate 1472 accepted1812
theorem accepted1813 : minorantGammaCheck GammaPanel1813.certificate 1472=true := by decide +kernel
noncomputable def cell1813 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1813.certificate 1472 accepted1813
theorem accepted1814 : minorantGammaCheck GammaPanel1814.certificate 1472=true := by decide +kernel
noncomputable def cell1814 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1814.certificate 1472 accepted1814
theorem accepted1815 : minorantGammaCheck GammaPanel1815.certificate 1472=true := by decide +kernel
noncomputable def cell1815 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1815.certificate 1472 accepted1815
noncomputable def cells : List CertifiedMinorantCell := [cell1808, cell1809, cell1810, cell1811, cell1812, cell1813, cell1814, cell1815]
theorem chainAccepted : minorantChainCheck (873/1000) (4369/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (873/1000) (4369/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0226
