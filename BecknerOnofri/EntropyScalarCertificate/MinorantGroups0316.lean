module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0316

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0316
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2528 : minorantGammaCheck GammaPanel2528.certificate 1621=true := by decide +kernel
noncomputable def cell2528 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2528.certificate 1621 accepted2528
theorem accepted2529 : minorantGammaCheck GammaPanel2529.certificate 1621=true := by decide +kernel
noncomputable def cell2529 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2529.certificate 1621 accepted2529
theorem accepted2530 : minorantGammaCheck GammaPanel2530.certificate 1621=true := by decide +kernel
noncomputable def cell2530 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2530.certificate 1621 accepted2530
theorem accepted2531 : minorantGammaCheck GammaPanel2531.certificate 1621=true := by decide +kernel
noncomputable def cell2531 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2531.certificate 1621 accepted2531
theorem accepted2532 : minorantGammaCheck GammaPanel2532.certificate 1621=true := by decide +kernel
noncomputable def cell2532 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2532.certificate 1621 accepted2532
theorem accepted2533 : minorantGammaCheck GammaPanel2533.certificate 1621=true := by decide +kernel
noncomputable def cell2533 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2533.certificate 1621 accepted2533
theorem accepted2534 : minorantGammaCheck GammaPanel2534.certificate 1621=true := by decide +kernel
noncomputable def cell2534 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2534.certificate 1621 accepted2534
theorem accepted2535 : minorantGammaCheck GammaPanel2535.certificate 1621=true := by decide +kernel
noncomputable def cell2535 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2535.certificate 1621 accepted2535
noncomputable def cells : List CertifiedMinorantCell := [cell2528, cell2529, cell2530, cell2531, cell2532, cell2533, cell2534, cell2535]
theorem chainAccepted : minorantChainCheck (993/1000) (24829/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (993/1000) (24829/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0316
