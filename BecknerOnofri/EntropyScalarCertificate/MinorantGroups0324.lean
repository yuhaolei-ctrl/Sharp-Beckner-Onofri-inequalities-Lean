module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0324

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0324
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2592 : minorantGammaCheck GammaPanel2592.certificate 1621=true := by decide +kernel
noncomputable def cell2592 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2592.certificate 1621 accepted2592
theorem accepted2593 : minorantGammaCheck GammaPanel2593.certificate 1621=true := by decide +kernel
noncomputable def cell2593 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2593.certificate 1621 accepted2593
theorem accepted2594 : minorantGammaCheck GammaPanel2594.certificate 1621=true := by decide +kernel
noncomputable def cell2594 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2594.certificate 1621 accepted2594
theorem accepted2595 : minorantGammaCheck GammaPanel2595.certificate 1621=true := by decide +kernel
noncomputable def cell2595 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2595.certificate 1621 accepted2595
theorem accepted2596 : minorantGammaCheck GammaPanel2596.certificate 1621=true := by decide +kernel
noncomputable def cell2596 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2596.certificate 1621 accepted2596
theorem accepted2597 : minorantGammaCheck GammaPanel2597.certificate 1621=true := by decide +kernel
noncomputable def cell2597 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2597.certificate 1621 accepted2597
theorem accepted2598 : minorantGammaCheck GammaPanel2598.certificate 1621=true := by decide +kernel
noncomputable def cell2598 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2598.certificate 1621 accepted2598
theorem accepted2599 : minorantGammaCheck GammaPanel2599.certificate 1621=true := by decide +kernel
noncomputable def cell2599 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2599.certificate 1621 accepted2599
noncomputable def cells : List CertifiedMinorantCell := [cell2592, cell2593, cell2594, cell2595, cell2596, cell2597, cell2598, cell2599]
theorem chainAccepted : minorantChainCheck (24857/25000) (24861/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24857/25000) (24861/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0324
