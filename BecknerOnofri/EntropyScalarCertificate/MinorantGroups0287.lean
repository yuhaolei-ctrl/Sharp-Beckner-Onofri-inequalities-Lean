module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0287

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0287
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2296 : minorantGammaCheck GammaPanel2296.certificate 1621=true := by decide +kernel
noncomputable def cell2296 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2296.certificate 1621 accepted2296
theorem accepted2297 : minorantGammaCheck GammaPanel2297.certificate 1621=true := by decide +kernel
noncomputable def cell2297 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2297.certificate 1621 accepted2297
theorem accepted2298 : minorantGammaCheck GammaPanel2298.certificate 1621=true := by decide +kernel
noncomputable def cell2298 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2298.certificate 1621 accepted2298
theorem accepted2299 : minorantGammaCheck GammaPanel2299.certificate 1621=true := by decide +kernel
noncomputable def cell2299 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2299.certificate 1621 accepted2299
theorem accepted2300 : minorantGammaCheck GammaPanel2300.certificate 1621=true := by decide +kernel
noncomputable def cell2300 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2300.certificate 1621 accepted2300
theorem accepted2301 : minorantGammaCheck GammaPanel2301.certificate 1621=true := by decide +kernel
noncomputable def cell2301 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2301.certificate 1621 accepted2301
theorem accepted2302 : minorantGammaCheck GammaPanel2302.certificate 1621=true := by decide +kernel
noncomputable def cell2302 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2302.certificate 1621 accepted2302
theorem accepted2303 : minorantGammaCheck GammaPanel2303.certificate 1621=true := by decide +kernel
noncomputable def cell2303 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2303.certificate 1621 accepted2303
noncomputable def cells : List CertifiedMinorantCell := [cell2296, cell2297, cell2298, cell2299, cell2300, cell2301, cell2302, cell2303]
theorem chainAccepted : minorantChainCheck (4909/5000) (4913/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4909/5000) (4913/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0287
