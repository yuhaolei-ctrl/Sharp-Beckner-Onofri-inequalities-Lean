module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0303

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0303
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2424 : minorantGammaCheck GammaPanel2424.certificate 1621=true := by decide +kernel
noncomputable def cell2424 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2424.certificate 1621 accepted2424
theorem accepted2425 : minorantGammaCheck GammaPanel2425.certificate 1621=true := by decide +kernel
noncomputable def cell2425 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2425.certificate 1621 accepted2425
theorem accepted2426 : minorantGammaCheck GammaPanel2426.certificate 1621=true := by decide +kernel
noncomputable def cell2426 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2426.certificate 1621 accepted2426
theorem accepted2427 : minorantGammaCheck GammaPanel2427.certificate 1621=true := by decide +kernel
noncomputable def cell2427 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2427.certificate 1621 accepted2427
theorem accepted2428 : minorantGammaCheck GammaPanel2428.certificate 1621=true := by decide +kernel
noncomputable def cell2428 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2428.certificate 1621 accepted2428
theorem accepted2429 : minorantGammaCheck GammaPanel2429.certificate 1621=true := by decide +kernel
noncomputable def cell2429 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2429.certificate 1621 accepted2429
theorem accepted2430 : minorantGammaCheck GammaPanel2430.certificate 1621=true := by decide +kernel
noncomputable def cell2430 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2430.certificate 1621 accepted2430
theorem accepted2431 : minorantGammaCheck GammaPanel2431.certificate 1621=true := by decide +kernel
noncomputable def cell2431 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2431.certificate 1621 accepted2431
noncomputable def cells : List CertifiedMinorantCell := [cell2424, cell2425, cell2426, cell2427, cell2428, cell2429, cell2430, cell2431]
theorem chainAccepted : minorantChainCheck (24773/25000) (24777/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24773/25000) (24777/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0303
