module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0053

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0053
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0424 : minorantGammaCheck GammaPanel0424.certificate 384=true := by decide +kernel
noncomputable def cell0424 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0424.certificate 384 accepted0424
theorem accepted0425 : minorantGammaCheck GammaPanel0425.certificate 385=true := by decide +kernel
noncomputable def cell0425 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0425.certificate 385 accepted0425
theorem accepted0426 : minorantGammaCheck GammaPanel0426.certificate 386=true := by decide +kernel
noncomputable def cell0426 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0426.certificate 386 accepted0426
theorem accepted0427 : minorantGammaCheck GammaPanel0427.certificate 387=true := by decide +kernel
noncomputable def cell0427 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0427.certificate 387 accepted0427
theorem accepted0428 : minorantGammaCheck GammaPanel0428.certificate 388=true := by decide +kernel
noncomputable def cell0428 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0428.certificate 388 accepted0428
theorem accepted0429 : minorantGammaCheck GammaPanel0429.certificate 389=true := by decide +kernel
noncomputable def cell0429 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0429.certificate 389 accepted0429
theorem accepted0430 : minorantGammaCheck GammaPanel0430.certificate 390=true := by decide +kernel
noncomputable def cell0430 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0430.certificate 390 accepted0430
theorem accepted0431 : minorantGammaCheck GammaPanel0431.certificate 391=true := by decide +kernel
noncomputable def cell0431 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0431.certificate 391 accepted0431
noncomputable def cells : List CertifiedMinorantCell := [cell0424, cell0425, cell0426, cell0427, cell0428, cell0429, cell0430, cell0431]
theorem chainAccepted : minorantChainCheck (1413/10000) (1429/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1413/10000) (1429/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0053
