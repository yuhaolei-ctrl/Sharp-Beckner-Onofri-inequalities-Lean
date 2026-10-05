module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0045

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0045
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0360 : minorantGammaCheck GammaPanel0360.certificate 320=true := by decide +kernel
noncomputable def cell0360 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0360.certificate 320 accepted0360
theorem accepted0361 : minorantGammaCheck GammaPanel0361.certificate 321=true := by decide +kernel
noncomputable def cell0361 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0361.certificate 321 accepted0361
theorem accepted0362 : minorantGammaCheck GammaPanel0362.certificate 322=true := by decide +kernel
noncomputable def cell0362 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0362.certificate 322 accepted0362
theorem accepted0363 : minorantGammaCheck GammaPanel0363.certificate 323=true := by decide +kernel
noncomputable def cell0363 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0363.certificate 323 accepted0363
theorem accepted0364 : minorantGammaCheck GammaPanel0364.certificate 324=true := by decide +kernel
noncomputable def cell0364 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0364.certificate 324 accepted0364
theorem accepted0365 : minorantGammaCheck GammaPanel0365.certificate 325=true := by decide +kernel
noncomputable def cell0365 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0365.certificate 325 accepted0365
theorem accepted0366 : minorantGammaCheck GammaPanel0366.certificate 326=true := by decide +kernel
noncomputable def cell0366 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0366.certificate 326 accepted0366
theorem accepted0367 : minorantGammaCheck GammaPanel0367.certificate 327=true := by decide +kernel
noncomputable def cell0367 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0367.certificate 327 accepted0367
noncomputable def cells : List CertifiedMinorantCell := [cell0360, cell0361, cell0362, cell0363, cell0364, cell0365, cell0366, cell0367]
theorem chainAccepted : minorantChainCheck (257/2000) (1301/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (257/2000) (1301/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0045
