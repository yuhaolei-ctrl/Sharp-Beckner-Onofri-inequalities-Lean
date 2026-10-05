module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0331

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0331
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2648 : minorantGammaCheck GammaPanel2648.certificate 1621=true := by decide +kernel
noncomputable def cell2648 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2648.certificate 1621 accepted2648
theorem accepted2649 : minorantGammaCheck GammaPanel2649.certificate 1621=true := by decide +kernel
noncomputable def cell2649 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2649.certificate 1621 accepted2649
theorem accepted2650 : minorantGammaCheck GammaPanel2650.certificate 1621=true := by decide +kernel
noncomputable def cell2650 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2650.certificate 1621 accepted2650
theorem accepted2651 : minorantGammaCheck GammaPanel2651.certificate 1621=true := by decide +kernel
noncomputable def cell2651 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2651.certificate 1621 accepted2651
theorem accepted2652 : minorantGammaCheck GammaPanel2652.certificate 1621=true := by decide +kernel
noncomputable def cell2652 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2652.certificate 1621 accepted2652
theorem accepted2653 : minorantGammaCheck GammaPanel2653.certificate 1621=true := by decide +kernel
noncomputable def cell2653 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2653.certificate 1621 accepted2653
theorem accepted2654 : minorantGammaCheck GammaPanel2654.certificate 1621=true := by decide +kernel
noncomputable def cell2654 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2654.certificate 1621 accepted2654
theorem accepted2655 : minorantGammaCheck GammaPanel2655.certificate 1621=true := by decide +kernel
noncomputable def cell2655 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2655.certificate 1621 accepted2655
noncomputable def cells : List CertifiedMinorantCell := [cell2648, cell2649, cell2650, cell2651, cell2652, cell2653, cell2654, cell2655]
theorem chainAccepted : minorantChainCheck (4977/5000) (24889/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4977/5000) (24889/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0331
