module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0073

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0073
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0584 : minorantGammaCheck GammaPanel0584.certificate 544=true := by decide +kernel
noncomputable def cell0584 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0584.certificate 544 accepted0584
theorem accepted0585 : minorantGammaCheck GammaPanel0585.certificate 545=true := by decide +kernel
noncomputable def cell0585 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0585.certificate 545 accepted0585
theorem accepted0586 : minorantGammaCheck GammaPanel0586.certificate 546=true := by decide +kernel
noncomputable def cell0586 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0586.certificate 546 accepted0586
theorem accepted0587 : minorantGammaCheck GammaPanel0587.certificate 547=true := by decide +kernel
noncomputable def cell0587 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0587.certificate 547 accepted0587
theorem accepted0588 : minorantGammaCheck GammaPanel0588.certificate 548=true := by decide +kernel
noncomputable def cell0588 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0588.certificate 548 accepted0588
theorem accepted0589 : minorantGammaCheck GammaPanel0589.certificate 549=true := by decide +kernel
noncomputable def cell0589 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0589.certificate 549 accepted0589
theorem accepted0590 : minorantGammaCheck GammaPanel0590.certificate 550=true := by decide +kernel
noncomputable def cell0590 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0590.certificate 550 accepted0590
theorem accepted0591 : minorantGammaCheck GammaPanel0591.certificate 551=true := by decide +kernel
noncomputable def cell0591 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0591.certificate 551 accepted0591
noncomputable def cells : List CertifiedMinorantCell := [cell0584, cell0585, cell0586, cell0587, cell0588, cell0589, cell0590, cell0591]
theorem chainAccepted : minorantChainCheck (1733/10000) (1749/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1733/10000) (1749/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0073
