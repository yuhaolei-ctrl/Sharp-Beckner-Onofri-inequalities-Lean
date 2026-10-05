module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0276

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0276
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2208 : minorantGammaCheck GammaPanel2208.certificate 1621=true := by decide +kernel
noncomputable def cell2208 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2208.certificate 1621 accepted2208
theorem accepted2209 : minorantGammaCheck GammaPanel2209.certificate 1621=true := by decide +kernel
noncomputable def cell2209 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2209.certificate 1621 accepted2209
theorem accepted2210 : minorantGammaCheck GammaPanel2210.certificate 1621=true := by decide +kernel
noncomputable def cell2210 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2210.certificate 1621 accepted2210
theorem accepted2211 : minorantGammaCheck GammaPanel2211.certificate 1621=true := by decide +kernel
noncomputable def cell2211 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2211.certificate 1621 accepted2211
theorem accepted2212 : minorantGammaCheck GammaPanel2212.certificate 1621=true := by decide +kernel
noncomputable def cell2212 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2212.certificate 1621 accepted2212
theorem accepted2213 : minorantGammaCheck GammaPanel2213.certificate 1621=true := by decide +kernel
noncomputable def cell2213 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2213.certificate 1621 accepted2213
theorem accepted2214 : minorantGammaCheck GammaPanel2214.certificate 1621=true := by decide +kernel
noncomputable def cell2214 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2214.certificate 1621 accepted2214
theorem accepted2215 : minorantGammaCheck GammaPanel2215.certificate 1621=true := by decide +kernel
noncomputable def cell2215 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2215.certificate 1621 accepted2215
noncomputable def cells : List CertifiedMinorantCell := [cell2208, cell2209, cell2210, cell2211, cell2212, cell2213, cell2214, cell2215]
theorem chainAccepted : minorantChainCheck (973/1000) (4869/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (973/1000) (4869/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0276
