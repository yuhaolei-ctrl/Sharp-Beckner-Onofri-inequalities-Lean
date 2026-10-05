import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0318
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0318
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2544 : minorantGammaCheck GammaPanel2544.certificate 1621=true := by decide +kernel
noncomputable def cell2544 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2544.certificate 1621 accepted2544
theorem accepted2545 : minorantGammaCheck GammaPanel2545.certificate 1621=true := by decide +kernel
noncomputable def cell2545 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2545.certificate 1621 accepted2545
theorem accepted2546 : minorantGammaCheck GammaPanel2546.certificate 1621=true := by decide +kernel
noncomputable def cell2546 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2546.certificate 1621 accepted2546
theorem accepted2547 : minorantGammaCheck GammaPanel2547.certificate 1621=true := by decide +kernel
noncomputable def cell2547 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2547.certificate 1621 accepted2547
theorem accepted2548 : minorantGammaCheck GammaPanel2548.certificate 1621=true := by decide +kernel
noncomputable def cell2548 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2548.certificate 1621 accepted2548
theorem accepted2549 : minorantGammaCheck GammaPanel2549.certificate 1621=true := by decide +kernel
noncomputable def cell2549 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2549.certificate 1621 accepted2549
theorem accepted2550 : minorantGammaCheck GammaPanel2550.certificate 1621=true := by decide +kernel
noncomputable def cell2550 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2550.certificate 1621 accepted2550
theorem accepted2551 : minorantGammaCheck GammaPanel2551.certificate 1621=true := by decide +kernel
noncomputable def cell2551 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2551.certificate 1621 accepted2551
noncomputable def cells : List CertifiedMinorantCell := [cell2544, cell2545, cell2546, cell2547, cell2548, cell2549, cell2550, cell2551]
theorem chainAccepted : minorantChainCheck (24833/25000) (24837/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24833/25000) (24837/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0318
