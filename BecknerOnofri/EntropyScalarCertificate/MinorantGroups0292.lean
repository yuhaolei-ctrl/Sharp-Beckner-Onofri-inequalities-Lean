module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0292

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0292
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2336 : minorantGammaCheck GammaPanel2336.certificate 1621=true := by decide +kernel
noncomputable def cell2336 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2336.certificate 1621 accepted2336
theorem accepted2337 : minorantGammaCheck GammaPanel2337.certificate 1621=true := by decide +kernel
noncomputable def cell2337 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2337.certificate 1621 accepted2337
theorem accepted2338 : minorantGammaCheck GammaPanel2338.certificate 1621=true := by decide +kernel
noncomputable def cell2338 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2338.certificate 1621 accepted2338
theorem accepted2339 : minorantGammaCheck GammaPanel2339.certificate 1621=true := by decide +kernel
noncomputable def cell2339 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2339.certificate 1621 accepted2339
theorem accepted2340 : minorantGammaCheck GammaPanel2340.certificate 1621=true := by decide +kernel
noncomputable def cell2340 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2340.certificate 1621 accepted2340
theorem accepted2341 : minorantGammaCheck GammaPanel2341.certificate 1621=true := by decide +kernel
noncomputable def cell2341 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2341.certificate 1621 accepted2341
theorem accepted2342 : minorantGammaCheck GammaPanel2342.certificate 1621=true := by decide +kernel
noncomputable def cell2342 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2342.certificate 1621 accepted2342
theorem accepted2343 : minorantGammaCheck GammaPanel2343.certificate 1621=true := by decide +kernel
noncomputable def cell2343 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2343.certificate 1621 accepted2343
noncomputable def cells : List CertifiedMinorantCell := [cell2336, cell2337, cell2338, cell2339, cell2340, cell2341, cell2342, cell2343]
theorem chainAccepted : minorantChainCheck (4929/5000) (4933/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4929/5000) (4933/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0292
