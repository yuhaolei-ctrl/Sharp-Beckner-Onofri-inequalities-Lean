module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0198

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0198
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1584 : minorantGammaCheck GammaPanel1584.certificate 1342=true := by decide +kernel
noncomputable def cell1584 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1584.certificate 1342 accepted1584
theorem accepted1585 : minorantGammaCheck GammaPanel1585.certificate 1343=true := by decide +kernel
noncomputable def cell1585 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1585.certificate 1343 accepted1585
theorem accepted1586 : minorantGammaCheck GammaPanel1586.certificate 1344=true := by decide +kernel
noncomputable def cell1586 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1586.certificate 1344 accepted1586
theorem accepted1587 : minorantGammaCheck GammaPanel1587.certificate 1345=true := by decide +kernel
noncomputable def cell1587 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1587.certificate 1345 accepted1587
theorem accepted1588 : minorantGammaCheck GammaPanel1588.certificate 1346=true := by decide +kernel
noncomputable def cell1588 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1588.certificate 1346 accepted1588
theorem accepted1589 : minorantGammaCheck GammaPanel1589.certificate 1347=true := by decide +kernel
noncomputable def cell1589 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1589.certificate 1347 accepted1589
theorem accepted1590 : minorantGammaCheck GammaPanel1590.certificate 1348=true := by decide +kernel
noncomputable def cell1590 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1590.certificate 1348 accepted1590
theorem accepted1591 : minorantGammaCheck GammaPanel1591.certificate 1349=true := by decide +kernel
noncomputable def cell1591 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1591.certificate 1349 accepted1591
noncomputable def cells : List CertifiedMinorantCell := [cell1584, cell1585, cell1586, cell1587, cell1588, cell1589, cell1590, cell1591]
theorem chainAccepted : minorantChainCheck (4253/5000) (4257/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4253/5000) (4257/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0198
