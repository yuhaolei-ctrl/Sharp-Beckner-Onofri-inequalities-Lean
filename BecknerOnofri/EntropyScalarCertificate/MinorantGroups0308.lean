import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0308
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0308
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2464 : minorantGammaCheck GammaPanel2464.certificate 1621=true := by decide +kernel
noncomputable def cell2464 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2464.certificate 1621 accepted2464
theorem accepted2465 : minorantGammaCheck GammaPanel2465.certificate 1621=true := by decide +kernel
noncomputable def cell2465 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2465.certificate 1621 accepted2465
theorem accepted2466 : minorantGammaCheck GammaPanel2466.certificate 1621=true := by decide +kernel
noncomputable def cell2466 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2466.certificate 1621 accepted2466
theorem accepted2467 : minorantGammaCheck GammaPanel2467.certificate 1621=true := by decide +kernel
noncomputable def cell2467 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2467.certificate 1621 accepted2467
theorem accepted2468 : minorantGammaCheck GammaPanel2468.certificate 1621=true := by decide +kernel
noncomputable def cell2468 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2468.certificate 1621 accepted2468
theorem accepted2469 : minorantGammaCheck GammaPanel2469.certificate 1621=true := by decide +kernel
noncomputable def cell2469 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2469.certificate 1621 accepted2469
theorem accepted2470 : minorantGammaCheck GammaPanel2470.certificate 1621=true := by decide +kernel
noncomputable def cell2470 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2470.certificate 1621 accepted2470
theorem accepted2471 : minorantGammaCheck GammaPanel2471.certificate 1621=true := by decide +kernel
noncomputable def cell2471 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2471.certificate 1621 accepted2471
noncomputable def cells : List CertifiedMinorantCell := [cell2464, cell2465, cell2466, cell2467, cell2468, cell2469, cell2470, cell2471]
theorem chainAccepted : minorantChainCheck (24793/25000) (24797/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24793/25000) (24797/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0308
