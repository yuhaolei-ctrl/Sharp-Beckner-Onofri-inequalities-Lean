module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0297

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0297
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2376 : minorantGammaCheck GammaPanel2376.certificate 1621=true := by decide +kernel
noncomputable def cell2376 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2376.certificate 1621 accepted2376
theorem accepted2377 : minorantGammaCheck GammaPanel2377.certificate 1621=true := by decide +kernel
noncomputable def cell2377 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2377.certificate 1621 accepted2377
theorem accepted2378 : minorantGammaCheck GammaPanel2378.certificate 1621=true := by decide +kernel
noncomputable def cell2378 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2378.certificate 1621 accepted2378
theorem accepted2379 : minorantGammaCheck GammaPanel2379.certificate 1621=true := by decide +kernel
noncomputable def cell2379 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2379.certificate 1621 accepted2379
theorem accepted2380 : minorantGammaCheck GammaPanel2380.certificate 1621=true := by decide +kernel
noncomputable def cell2380 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2380.certificate 1621 accepted2380
theorem accepted2381 : minorantGammaCheck GammaPanel2381.certificate 1621=true := by decide +kernel
noncomputable def cell2381 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2381.certificate 1621 accepted2381
theorem accepted2382 : minorantGammaCheck GammaPanel2382.certificate 1621=true := by decide +kernel
noncomputable def cell2382 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2382.certificate 1621 accepted2382
theorem accepted2383 : minorantGammaCheck GammaPanel2383.certificate 1621=true := by decide +kernel
noncomputable def cell2383 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2383.certificate 1621 accepted2383
noncomputable def cells : List CertifiedMinorantCell := [cell2376, cell2377, cell2378, cell2379, cell2380, cell2381, cell2382, cell2383]
theorem chainAccepted : minorantChainCheck (4949/5000) (24753/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4949/5000) (24753/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0297
