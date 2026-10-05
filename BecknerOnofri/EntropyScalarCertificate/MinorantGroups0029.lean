module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0029

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0029
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0232 : minorantGammaCheck GammaPanel0232.certificate 192=true := by decide +kernel
noncomputable def cell0232 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0232.certificate 192 accepted0232
theorem accepted0233 : minorantGammaCheck GammaPanel0233.certificate 193=true := by decide +kernel
noncomputable def cell0233 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0233.certificate 193 accepted0233
theorem accepted0234 : minorantGammaCheck GammaPanel0234.certificate 194=true := by decide +kernel
noncomputable def cell0234 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0234.certificate 194 accepted0234
theorem accepted0235 : minorantGammaCheck GammaPanel0235.certificate 195=true := by decide +kernel
noncomputable def cell0235 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0235.certificate 195 accepted0235
theorem accepted0236 : minorantGammaCheck GammaPanel0236.certificate 196=true := by decide +kernel
noncomputable def cell0236 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0236.certificate 196 accepted0236
theorem accepted0237 : minorantGammaCheck GammaPanel0237.certificate 197=true := by decide +kernel
noncomputable def cell0237 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0237.certificate 197 accepted0237
theorem accepted0238 : minorantGammaCheck GammaPanel0238.certificate 198=true := by decide +kernel
noncomputable def cell0238 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0238.certificate 198 accepted0238
theorem accepted0239 : minorantGammaCheck GammaPanel0239.certificate 199=true := by decide +kernel
noncomputable def cell0239 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0239.certificate 199 accepted0239
noncomputable def cells : List CertifiedMinorantCell := [cell0232, cell0233, cell0234, cell0235, cell0236, cell0237, cell0238, cell0239]
theorem chainAccepted : minorantChainCheck (1029/10000) (209/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1029/10000) (209/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0029
