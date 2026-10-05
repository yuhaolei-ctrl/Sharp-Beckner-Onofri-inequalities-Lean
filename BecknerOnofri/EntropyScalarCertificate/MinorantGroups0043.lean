module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0043

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0043
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0344 : minorantGammaCheck GammaPanel0344.certificate 304=true := by decide +kernel
noncomputable def cell0344 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0344.certificate 304 accepted0344
theorem accepted0345 : minorantGammaCheck GammaPanel0345.certificate 305=true := by decide +kernel
noncomputable def cell0345 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0345.certificate 305 accepted0345
theorem accepted0346 : minorantGammaCheck GammaPanel0346.certificate 306=true := by decide +kernel
noncomputable def cell0346 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0346.certificate 306 accepted0346
theorem accepted0347 : minorantGammaCheck GammaPanel0347.certificate 307=true := by decide +kernel
noncomputable def cell0347 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0347.certificate 307 accepted0347
theorem accepted0348 : minorantGammaCheck GammaPanel0348.certificate 308=true := by decide +kernel
noncomputable def cell0348 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0348.certificate 308 accepted0348
theorem accepted0349 : minorantGammaCheck GammaPanel0349.certificate 309=true := by decide +kernel
noncomputable def cell0349 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0349.certificate 309 accepted0349
theorem accepted0350 : minorantGammaCheck GammaPanel0350.certificate 310=true := by decide +kernel
noncomputable def cell0350 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0350.certificate 310 accepted0350
theorem accepted0351 : minorantGammaCheck GammaPanel0351.certificate 311=true := by decide +kernel
noncomputable def cell0351 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0351.certificate 311 accepted0351
noncomputable def cells : List CertifiedMinorantCell := [cell0344, cell0345, cell0346, cell0347, cell0348, cell0349, cell0350, cell0351]
theorem chainAccepted : minorantChainCheck (1253/10000) (1269/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1253/10000) (1269/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0043
