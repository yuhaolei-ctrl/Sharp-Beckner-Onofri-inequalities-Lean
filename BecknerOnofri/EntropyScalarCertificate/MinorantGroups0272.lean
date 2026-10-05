module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0272

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0272
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2176 : minorantGammaCheck GammaPanel2176.certificate 1621=true := by decide +kernel
noncomputable def cell2176 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2176.certificate 1621 accepted2176
theorem accepted2177 : minorantGammaCheck GammaPanel2177.certificate 1621=true := by decide +kernel
noncomputable def cell2177 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2177.certificate 1621 accepted2177
theorem accepted2178 : minorantGammaCheck GammaPanel2178.certificate 1621=true := by decide +kernel
noncomputable def cell2178 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2178.certificate 1621 accepted2178
theorem accepted2179 : minorantGammaCheck GammaPanel2179.certificate 1621=true := by decide +kernel
noncomputable def cell2179 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2179.certificate 1621 accepted2179
theorem accepted2180 : minorantGammaCheck GammaPanel2180.certificate 1621=true := by decide +kernel
noncomputable def cell2180 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2180.certificate 1621 accepted2180
theorem accepted2181 : minorantGammaCheck GammaPanel2181.certificate 1621=true := by decide +kernel
noncomputable def cell2181 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2181.certificate 1621 accepted2181
theorem accepted2182 : minorantGammaCheck GammaPanel2182.certificate 1621=true := by decide +kernel
noncomputable def cell2182 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2182.certificate 1621 accepted2182
theorem accepted2183 : minorantGammaCheck GammaPanel2183.certificate 1621=true := by decide +kernel
noncomputable def cell2183 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2183.certificate 1621 accepted2183
noncomputable def cells : List CertifiedMinorantCell := [cell2176, cell2177, cell2178, cell2179, cell2180, cell2181, cell2182, cell2183]
theorem chainAccepted : minorantChainCheck (4849/5000) (4853/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4849/5000) (4853/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0272
