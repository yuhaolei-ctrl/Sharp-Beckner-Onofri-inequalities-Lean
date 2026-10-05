module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0039

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0039
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0312 : minorantGammaCheck GammaPanel0312.certificate 272=true := by decide +kernel
noncomputable def cell0312 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0312.certificate 272 accepted0312
theorem accepted0313 : minorantGammaCheck GammaPanel0313.certificate 273=true := by decide +kernel
noncomputable def cell0313 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0313.certificate 273 accepted0313
theorem accepted0314 : minorantGammaCheck GammaPanel0314.certificate 274=true := by decide +kernel
noncomputable def cell0314 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0314.certificate 274 accepted0314
theorem accepted0315 : minorantGammaCheck GammaPanel0315.certificate 275=true := by decide +kernel
noncomputable def cell0315 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0315.certificate 275 accepted0315
theorem accepted0316 : minorantGammaCheck GammaPanel0316.certificate 276=true := by decide +kernel
noncomputable def cell0316 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0316.certificate 276 accepted0316
theorem accepted0317 : minorantGammaCheck GammaPanel0317.certificate 277=true := by decide +kernel
noncomputable def cell0317 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0317.certificate 277 accepted0317
theorem accepted0318 : minorantGammaCheck GammaPanel0318.certificate 278=true := by decide +kernel
noncomputable def cell0318 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0318.certificate 278 accepted0318
theorem accepted0319 : minorantGammaCheck GammaPanel0319.certificate 279=true := by decide +kernel
noncomputable def cell0319 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0319.certificate 279 accepted0319
noncomputable def cells : List CertifiedMinorantCell := [cell0312, cell0313, cell0314, cell0315, cell0316, cell0317, cell0318, cell0319]
theorem chainAccepted : minorantChainCheck (1189/10000) (241/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1189/10000) (241/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0039
