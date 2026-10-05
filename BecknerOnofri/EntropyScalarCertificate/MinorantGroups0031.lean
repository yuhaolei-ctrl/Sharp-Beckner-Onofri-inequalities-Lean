module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0031

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0031
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0248 : minorantGammaCheck GammaPanel0248.certificate 208=true := by decide +kernel
noncomputable def cell0248 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0248.certificate 208 accepted0248
theorem accepted0249 : minorantGammaCheck GammaPanel0249.certificate 209=true := by decide +kernel
noncomputable def cell0249 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0249.certificate 209 accepted0249
theorem accepted0250 : minorantGammaCheck GammaPanel0250.certificate 210=true := by decide +kernel
noncomputable def cell0250 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0250.certificate 210 accepted0250
theorem accepted0251 : minorantGammaCheck GammaPanel0251.certificate 211=true := by decide +kernel
noncomputable def cell0251 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0251.certificate 211 accepted0251
theorem accepted0252 : minorantGammaCheck GammaPanel0252.certificate 212=true := by decide +kernel
noncomputable def cell0252 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0252.certificate 212 accepted0252
theorem accepted0253 : minorantGammaCheck GammaPanel0253.certificate 213=true := by decide +kernel
noncomputable def cell0253 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0253.certificate 213 accepted0253
theorem accepted0254 : minorantGammaCheck GammaPanel0254.certificate 214=true := by decide +kernel
noncomputable def cell0254 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0254.certificate 214 accepted0254
theorem accepted0255 : minorantGammaCheck GammaPanel0255.certificate 215=true := by decide +kernel
noncomputable def cell0255 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0255.certificate 215 accepted0255
noncomputable def cells : List CertifiedMinorantCell := [cell0248, cell0249, cell0250, cell0251, cell0252, cell0253, cell0254, cell0255]
theorem chainAccepted : minorantChainCheck (1061/10000) (1077/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1061/10000) (1077/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0031
