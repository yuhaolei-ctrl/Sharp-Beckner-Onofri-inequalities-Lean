module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0314

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0314
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2512 : minorantGammaCheck GammaPanel2512.certificate 1621=true := by decide +kernel
noncomputable def cell2512 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2512.certificate 1621 accepted2512
theorem accepted2513 : minorantGammaCheck GammaPanel2513.certificate 1621=true := by decide +kernel
noncomputable def cell2513 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2513.certificate 1621 accepted2513
theorem accepted2514 : minorantGammaCheck GammaPanel2514.certificate 1621=true := by decide +kernel
noncomputable def cell2514 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2514.certificate 1621 accepted2514
theorem accepted2515 : minorantGammaCheck GammaPanel2515.certificate 1621=true := by decide +kernel
noncomputable def cell2515 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2515.certificate 1621 accepted2515
theorem accepted2516 : minorantGammaCheck GammaPanel2516.certificate 1621=true := by decide +kernel
noncomputable def cell2516 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2516.certificate 1621 accepted2516
theorem accepted2517 : minorantGammaCheck GammaPanel2517.certificate 1621=true := by decide +kernel
noncomputable def cell2517 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2517.certificate 1621 accepted2517
theorem accepted2518 : minorantGammaCheck GammaPanel2518.certificate 1621=true := by decide +kernel
noncomputable def cell2518 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2518.certificate 1621 accepted2518
theorem accepted2519 : minorantGammaCheck GammaPanel2519.certificate 1621=true := by decide +kernel
noncomputable def cell2519 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2519.certificate 1621 accepted2519
noncomputable def cells : List CertifiedMinorantCell := [cell2512, cell2513, cell2514, cell2515, cell2516, cell2517, cell2518, cell2519]
theorem chainAccepted : minorantChainCheck (24817/25000) (24821/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24817/25000) (24821/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0314
