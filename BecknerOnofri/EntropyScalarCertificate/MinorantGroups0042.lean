module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0042

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0042
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0336 : minorantGammaCheck GammaPanel0336.certificate 296=true := by decide +kernel
noncomputable def cell0336 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0336.certificate 296 accepted0336
theorem accepted0337 : minorantGammaCheck GammaPanel0337.certificate 297=true := by decide +kernel
noncomputable def cell0337 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0337.certificate 297 accepted0337
theorem accepted0338 : minorantGammaCheck GammaPanel0338.certificate 298=true := by decide +kernel
noncomputable def cell0338 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0338.certificate 298 accepted0338
theorem accepted0339 : minorantGammaCheck GammaPanel0339.certificate 299=true := by decide +kernel
noncomputable def cell0339 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0339.certificate 299 accepted0339
theorem accepted0340 : minorantGammaCheck GammaPanel0340.certificate 300=true := by decide +kernel
noncomputable def cell0340 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0340.certificate 300 accepted0340
theorem accepted0341 : minorantGammaCheck GammaPanel0341.certificate 301=true := by decide +kernel
noncomputable def cell0341 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0341.certificate 301 accepted0341
theorem accepted0342 : minorantGammaCheck GammaPanel0342.certificate 302=true := by decide +kernel
noncomputable def cell0342 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0342.certificate 302 accepted0342
theorem accepted0343 : minorantGammaCheck GammaPanel0343.certificate 303=true := by decide +kernel
noncomputable def cell0343 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0343.certificate 303 accepted0343
noncomputable def cells : List CertifiedMinorantCell := [cell0336, cell0337, cell0338, cell0339, cell0340, cell0341, cell0342, cell0343]
theorem chainAccepted : minorantChainCheck (1237/10000) (1253/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1237/10000) (1253/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0042
