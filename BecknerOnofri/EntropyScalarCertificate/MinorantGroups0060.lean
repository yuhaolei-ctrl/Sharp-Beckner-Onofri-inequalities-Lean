module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0060

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0060
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0480 : minorantGammaCheck GammaPanel0480.certificate 440=true := by decide +kernel
noncomputable def cell0480 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0480.certificate 440 accepted0480
theorem accepted0481 : minorantGammaCheck GammaPanel0481.certificate 441=true := by decide +kernel
noncomputable def cell0481 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0481.certificate 441 accepted0481
theorem accepted0482 : minorantGammaCheck GammaPanel0482.certificate 442=true := by decide +kernel
noncomputable def cell0482 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0482.certificate 442 accepted0482
theorem accepted0483 : minorantGammaCheck GammaPanel0483.certificate 443=true := by decide +kernel
noncomputable def cell0483 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0483.certificate 443 accepted0483
theorem accepted0484 : minorantGammaCheck GammaPanel0484.certificate 444=true := by decide +kernel
noncomputable def cell0484 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0484.certificate 444 accepted0484
theorem accepted0485 : minorantGammaCheck GammaPanel0485.certificate 445=true := by decide +kernel
noncomputable def cell0485 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0485.certificate 445 accepted0485
theorem accepted0486 : minorantGammaCheck GammaPanel0486.certificate 446=true := by decide +kernel
noncomputable def cell0486 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0486.certificate 446 accepted0486
theorem accepted0487 : minorantGammaCheck GammaPanel0487.certificate 447=true := by decide +kernel
noncomputable def cell0487 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0487.certificate 447 accepted0487
noncomputable def cells : List CertifiedMinorantCell := [cell0480, cell0481, cell0482, cell0483, cell0484, cell0485, cell0486, cell0487]
theorem chainAccepted : minorantChainCheck (61/400) (1541/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (61/400) (1541/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0060
