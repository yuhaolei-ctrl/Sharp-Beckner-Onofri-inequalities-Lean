module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0050

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0050
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0400 : minorantGammaCheck GammaPanel0400.certificate 360=true := by decide +kernel
noncomputable def cell0400 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0400.certificate 360 accepted0400
theorem accepted0401 : minorantGammaCheck GammaPanel0401.certificate 361=true := by decide +kernel
noncomputable def cell0401 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0401.certificate 361 accepted0401
theorem accepted0402 : minorantGammaCheck GammaPanel0402.certificate 362=true := by decide +kernel
noncomputable def cell0402 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0402.certificate 362 accepted0402
theorem accepted0403 : minorantGammaCheck GammaPanel0403.certificate 363=true := by decide +kernel
noncomputable def cell0403 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0403.certificate 363 accepted0403
theorem accepted0404 : minorantGammaCheck GammaPanel0404.certificate 364=true := by decide +kernel
noncomputable def cell0404 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0404.certificate 364 accepted0404
theorem accepted0405 : minorantGammaCheck GammaPanel0405.certificate 365=true := by decide +kernel
noncomputable def cell0405 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0405.certificate 365 accepted0405
theorem accepted0406 : minorantGammaCheck GammaPanel0406.certificate 366=true := by decide +kernel
noncomputable def cell0406 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0406.certificate 366 accepted0406
theorem accepted0407 : minorantGammaCheck GammaPanel0407.certificate 367=true := by decide +kernel
noncomputable def cell0407 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0407.certificate 367 accepted0407
noncomputable def cells : List CertifiedMinorantCell := [cell0400, cell0401, cell0402, cell0403, cell0404, cell0405, cell0406, cell0407]
theorem chainAccepted : minorantChainCheck (273/2000) (1381/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (273/2000) (1381/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0050
