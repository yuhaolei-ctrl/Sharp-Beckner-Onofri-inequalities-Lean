module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0309

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0309
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2472 : minorantGammaCheck GammaPanel2472.certificate 1621=true := by decide +kernel
noncomputable def cell2472 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2472.certificate 1621 accepted2472
theorem accepted2473 : minorantGammaCheck GammaPanel2473.certificate 1621=true := by decide +kernel
noncomputable def cell2473 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2473.certificate 1621 accepted2473
theorem accepted2474 : minorantGammaCheck GammaPanel2474.certificate 1621=true := by decide +kernel
noncomputable def cell2474 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2474.certificate 1621 accepted2474
theorem accepted2475 : minorantGammaCheck GammaPanel2475.certificate 1621=true := by decide +kernel
noncomputable def cell2475 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2475.certificate 1621 accepted2475
theorem accepted2476 : minorantGammaCheck GammaPanel2476.certificate 1621=true := by decide +kernel
noncomputable def cell2476 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2476.certificate 1621 accepted2476
theorem accepted2477 : minorantGammaCheck GammaPanel2477.certificate 1621=true := by decide +kernel
noncomputable def cell2477 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2477.certificate 1621 accepted2477
theorem accepted2478 : minorantGammaCheck GammaPanel2478.certificate 1621=true := by decide +kernel
noncomputable def cell2478 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2478.certificate 1621 accepted2478
theorem accepted2479 : minorantGammaCheck GammaPanel2479.certificate 1621=true := by decide +kernel
noncomputable def cell2479 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2479.certificate 1621 accepted2479
noncomputable def cells : List CertifiedMinorantCell := [cell2472, cell2473, cell2474, cell2475, cell2476, cell2477, cell2478, cell2479]
theorem chainAccepted : minorantChainCheck (24797/25000) (24801/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24797/25000) (24801/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0309
