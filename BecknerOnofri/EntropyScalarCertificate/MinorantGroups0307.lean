module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0307

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0307
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2456 : minorantGammaCheck GammaPanel2456.certificate 1621=true := by decide +kernel
noncomputable def cell2456 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2456.certificate 1621 accepted2456
theorem accepted2457 : minorantGammaCheck GammaPanel2457.certificate 1621=true := by decide +kernel
noncomputable def cell2457 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2457.certificate 1621 accepted2457
theorem accepted2458 : minorantGammaCheck GammaPanel2458.certificate 1621=true := by decide +kernel
noncomputable def cell2458 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2458.certificate 1621 accepted2458
theorem accepted2459 : minorantGammaCheck GammaPanel2459.certificate 1621=true := by decide +kernel
noncomputable def cell2459 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2459.certificate 1621 accepted2459
theorem accepted2460 : minorantGammaCheck GammaPanel2460.certificate 1621=true := by decide +kernel
noncomputable def cell2460 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2460.certificate 1621 accepted2460
theorem accepted2461 : minorantGammaCheck GammaPanel2461.certificate 1621=true := by decide +kernel
noncomputable def cell2461 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2461.certificate 1621 accepted2461
theorem accepted2462 : minorantGammaCheck GammaPanel2462.certificate 1621=true := by decide +kernel
noncomputable def cell2462 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2462.certificate 1621 accepted2462
theorem accepted2463 : minorantGammaCheck GammaPanel2463.certificate 1621=true := by decide +kernel
noncomputable def cell2463 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2463.certificate 1621 accepted2463
noncomputable def cells : List CertifiedMinorantCell := [cell2456, cell2457, cell2458, cell2459, cell2460, cell2461, cell2462, cell2463]
theorem chainAccepted : minorantChainCheck (24789/25000) (24793/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24789/25000) (24793/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0307
