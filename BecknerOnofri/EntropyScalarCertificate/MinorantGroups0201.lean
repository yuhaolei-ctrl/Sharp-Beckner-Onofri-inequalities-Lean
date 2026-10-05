module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0201

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0201
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1608 : minorantGammaCheck GammaPanel1608.certificate 1366=true := by decide +kernel
noncomputable def cell1608 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1608.certificate 1366 accepted1608
theorem accepted1609 : minorantGammaCheck GammaPanel1609.certificate 1367=true := by decide +kernel
noncomputable def cell1609 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1609.certificate 1367 accepted1609
theorem accepted1610 : minorantGammaCheck GammaPanel1610.certificate 1368=true := by decide +kernel
noncomputable def cell1610 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1610.certificate 1368 accepted1610
theorem accepted1611 : minorantGammaCheck GammaPanel1611.certificate 1369=true := by decide +kernel
noncomputable def cell1611 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1611.certificate 1369 accepted1611
theorem accepted1612 : minorantGammaCheck GammaPanel1612.certificate 1370=true := by decide +kernel
noncomputable def cell1612 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1612.certificate 1370 accepted1612
theorem accepted1613 : minorantGammaCheck GammaPanel1613.certificate 1371=true := by decide +kernel
noncomputable def cell1613 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1613.certificate 1371 accepted1613
theorem accepted1614 : minorantGammaCheck GammaPanel1614.certificate 1372=true := by decide +kernel
noncomputable def cell1614 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1614.certificate 1372 accepted1614
theorem accepted1615 : minorantGammaCheck GammaPanel1615.certificate 1373=true := by decide +kernel
noncomputable def cell1615 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1615.certificate 1373 accepted1615
noncomputable def cells : List CertifiedMinorantCell := [cell1608, cell1609, cell1610, cell1611, cell1612, cell1613, cell1614, cell1615]
theorem chainAccepted : minorantChainCheck (853/1000) (4269/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (853/1000) (4269/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0201
