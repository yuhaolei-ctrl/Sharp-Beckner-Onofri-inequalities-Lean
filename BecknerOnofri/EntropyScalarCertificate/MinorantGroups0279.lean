module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0279

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0279
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2232 : minorantGammaCheck GammaPanel2232.certificate 1621=true := by decide +kernel
noncomputable def cell2232 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2232.certificate 1621 accepted2232
theorem accepted2233 : minorantGammaCheck GammaPanel2233.certificate 1621=true := by decide +kernel
noncomputable def cell2233 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2233.certificate 1621 accepted2233
theorem accepted2234 : minorantGammaCheck GammaPanel2234.certificate 1621=true := by decide +kernel
noncomputable def cell2234 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2234.certificate 1621 accepted2234
theorem accepted2235 : minorantGammaCheck GammaPanel2235.certificate 1621=true := by decide +kernel
noncomputable def cell2235 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2235.certificate 1621 accepted2235
theorem accepted2236 : minorantGammaCheck GammaPanel2236.certificate 1621=true := by decide +kernel
noncomputable def cell2236 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2236.certificate 1621 accepted2236
theorem accepted2237 : minorantGammaCheck GammaPanel2237.certificate 1621=true := by decide +kernel
noncomputable def cell2237 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2237.certificate 1621 accepted2237
theorem accepted2238 : minorantGammaCheck GammaPanel2238.certificate 1621=true := by decide +kernel
noncomputable def cell2238 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2238.certificate 1621 accepted2238
theorem accepted2239 : minorantGammaCheck GammaPanel2239.certificate 1621=true := by decide +kernel
noncomputable def cell2239 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2239.certificate 1621 accepted2239
noncomputable def cells : List CertifiedMinorantCell := [cell2232, cell2233, cell2234, cell2235, cell2236, cell2237, cell2238, cell2239]
theorem chainAccepted : minorantChainCheck (4877/5000) (4881/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4877/5000) (4881/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0279
