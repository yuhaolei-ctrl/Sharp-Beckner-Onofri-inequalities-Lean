module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0299

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0299
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2392 : minorantGammaCheck GammaPanel2392.certificate 1621=true := by decide +kernel
noncomputable def cell2392 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2392.certificate 1621 accepted2392
theorem accepted2393 : minorantGammaCheck GammaPanel2393.certificate 1621=true := by decide +kernel
noncomputable def cell2393 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2393.certificate 1621 accepted2393
theorem accepted2394 : minorantGammaCheck GammaPanel2394.certificate 1621=true := by decide +kernel
noncomputable def cell2394 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2394.certificate 1621 accepted2394
theorem accepted2395 : minorantGammaCheck GammaPanel2395.certificate 1621=true := by decide +kernel
noncomputable def cell2395 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2395.certificate 1621 accepted2395
theorem accepted2396 : minorantGammaCheck GammaPanel2396.certificate 1621=true := by decide +kernel
noncomputable def cell2396 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2396.certificate 1621 accepted2396
theorem accepted2397 : minorantGammaCheck GammaPanel2397.certificate 1621=true := by decide +kernel
noncomputable def cell2397 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2397.certificate 1621 accepted2397
theorem accepted2398 : minorantGammaCheck GammaPanel2398.certificate 1621=true := by decide +kernel
noncomputable def cell2398 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2398.certificate 1621 accepted2398
theorem accepted2399 : minorantGammaCheck GammaPanel2399.certificate 1621=true := by decide +kernel
noncomputable def cell2399 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2399.certificate 1621 accepted2399
noncomputable def cells : List CertifiedMinorantCell := [cell2392, cell2393, cell2394, cell2395, cell2396, cell2397, cell2398, cell2399]
theorem chainAccepted : minorantChainCheck (24757/25000) (24761/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24757/25000) (24761/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0299
