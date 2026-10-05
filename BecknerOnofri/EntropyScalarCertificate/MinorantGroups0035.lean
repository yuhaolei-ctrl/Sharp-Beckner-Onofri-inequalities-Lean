module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0035

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0035
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0280 : minorantGammaCheck GammaPanel0280.certificate 240=true := by decide +kernel
noncomputable def cell0280 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0280.certificate 240 accepted0280
theorem accepted0281 : minorantGammaCheck GammaPanel0281.certificate 241=true := by decide +kernel
noncomputable def cell0281 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0281.certificate 241 accepted0281
theorem accepted0282 : minorantGammaCheck GammaPanel0282.certificate 242=true := by decide +kernel
noncomputable def cell0282 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0282.certificate 242 accepted0282
theorem accepted0283 : minorantGammaCheck GammaPanel0283.certificate 243=true := by decide +kernel
noncomputable def cell0283 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0283.certificate 243 accepted0283
theorem accepted0284 : minorantGammaCheck GammaPanel0284.certificate 244=true := by decide +kernel
noncomputable def cell0284 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0284.certificate 244 accepted0284
theorem accepted0285 : minorantGammaCheck GammaPanel0285.certificate 245=true := by decide +kernel
noncomputable def cell0285 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0285.certificate 245 accepted0285
theorem accepted0286 : minorantGammaCheck GammaPanel0286.certificate 246=true := by decide +kernel
noncomputable def cell0286 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0286.certificate 246 accepted0286
theorem accepted0287 : minorantGammaCheck GammaPanel0287.certificate 247=true := by decide +kernel
noncomputable def cell0287 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0287.certificate 247 accepted0287
noncomputable def cells : List CertifiedMinorantCell := [cell0280, cell0281, cell0282, cell0283, cell0284, cell0285, cell0286, cell0287]
theorem chainAccepted : minorantChainCheck (9/80) (1141/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (9/80) (1141/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0035
