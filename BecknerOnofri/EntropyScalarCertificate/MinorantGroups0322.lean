import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0322
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0322
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2576 : minorantGammaCheck GammaPanel2576.certificate 1621=true := by decide +kernel
noncomputable def cell2576 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2576.certificate 1621 accepted2576
theorem accepted2577 : minorantGammaCheck GammaPanel2577.certificate 1621=true := by decide +kernel
noncomputable def cell2577 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2577.certificate 1621 accepted2577
theorem accepted2578 : minorantGammaCheck GammaPanel2578.certificate 1621=true := by decide +kernel
noncomputable def cell2578 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2578.certificate 1621 accepted2578
theorem accepted2579 : minorantGammaCheck GammaPanel2579.certificate 1621=true := by decide +kernel
noncomputable def cell2579 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2579.certificate 1621 accepted2579
theorem accepted2580 : minorantGammaCheck GammaPanel2580.certificate 1621=true := by decide +kernel
noncomputable def cell2580 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2580.certificate 1621 accepted2580
theorem accepted2581 : minorantGammaCheck GammaPanel2581.certificate 1621=true := by decide +kernel
noncomputable def cell2581 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2581.certificate 1621 accepted2581
theorem accepted2582 : minorantGammaCheck GammaPanel2582.certificate 1621=true := by decide +kernel
noncomputable def cell2582 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2582.certificate 1621 accepted2582
theorem accepted2583 : minorantGammaCheck GammaPanel2583.certificate 1621=true := by decide +kernel
noncomputable def cell2583 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2583.certificate 1621 accepted2583
noncomputable def cells : List CertifiedMinorantCell := [cell2576, cell2577, cell2578, cell2579, cell2580, cell2581, cell2582, cell2583]
theorem chainAccepted : minorantChainCheck (24849/25000) (24853/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24849/25000) (24853/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0322
