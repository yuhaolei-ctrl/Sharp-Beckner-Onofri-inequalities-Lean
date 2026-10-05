module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0327

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0327
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2616 : minorantGammaCheck GammaPanel2616.certificate 1621=true := by decide +kernel
noncomputable def cell2616 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2616.certificate 1621 accepted2616
theorem accepted2617 : minorantGammaCheck GammaPanel2617.certificate 1621=true := by decide +kernel
noncomputable def cell2617 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2617.certificate 1621 accepted2617
theorem accepted2618 : minorantGammaCheck GammaPanel2618.certificate 1621=true := by decide +kernel
noncomputable def cell2618 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2618.certificate 1621 accepted2618
theorem accepted2619 : minorantGammaCheck GammaPanel2619.certificate 1621=true := by decide +kernel
noncomputable def cell2619 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2619.certificate 1621 accepted2619
theorem accepted2620 : minorantGammaCheck GammaPanel2620.certificate 1621=true := by decide +kernel
noncomputable def cell2620 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2620.certificate 1621 accepted2620
theorem accepted2621 : minorantGammaCheck GammaPanel2621.certificate 1621=true := by decide +kernel
noncomputable def cell2621 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2621.certificate 1621 accepted2621
theorem accepted2622 : minorantGammaCheck GammaPanel2622.certificate 1621=true := by decide +kernel
noncomputable def cell2622 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2622.certificate 1621 accepted2622
theorem accepted2623 : minorantGammaCheck GammaPanel2623.certificate 1621=true := by decide +kernel
noncomputable def cell2623 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2623.certificate 1621 accepted2623
noncomputable def cells : List CertifiedMinorantCell := [cell2616, cell2617, cell2618, cell2619, cell2620, cell2621, cell2622, cell2623]
theorem chainAccepted : minorantChainCheck (24869/25000) (24873/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24869/25000) (24873/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0327
