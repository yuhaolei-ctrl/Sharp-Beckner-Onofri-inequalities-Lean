module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0321

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0321
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2568 : minorantGammaCheck GammaPanel2568.certificate 1621=true := by decide +kernel
noncomputable def cell2568 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2568.certificate 1621 accepted2568
theorem accepted2569 : minorantGammaCheck GammaPanel2569.certificate 1621=true := by decide +kernel
noncomputable def cell2569 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2569.certificate 1621 accepted2569
theorem accepted2570 : minorantGammaCheck GammaPanel2570.certificate 1621=true := by decide +kernel
noncomputable def cell2570 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2570.certificate 1621 accepted2570
theorem accepted2571 : minorantGammaCheck GammaPanel2571.certificate 1621=true := by decide +kernel
noncomputable def cell2571 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2571.certificate 1621 accepted2571
theorem accepted2572 : minorantGammaCheck GammaPanel2572.certificate 1621=true := by decide +kernel
noncomputable def cell2572 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2572.certificate 1621 accepted2572
theorem accepted2573 : minorantGammaCheck GammaPanel2573.certificate 1621=true := by decide +kernel
noncomputable def cell2573 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2573.certificate 1621 accepted2573
theorem accepted2574 : minorantGammaCheck GammaPanel2574.certificate 1621=true := by decide +kernel
noncomputable def cell2574 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2574.certificate 1621 accepted2574
theorem accepted2575 : minorantGammaCheck GammaPanel2575.certificate 1621=true := by decide +kernel
noncomputable def cell2575 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2575.certificate 1621 accepted2575
noncomputable def cells : List CertifiedMinorantCell := [cell2568, cell2569, cell2570, cell2571, cell2572, cell2573, cell2574, cell2575]
theorem chainAccepted : minorantChainCheck (4969/5000) (24849/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4969/5000) (24849/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0321
