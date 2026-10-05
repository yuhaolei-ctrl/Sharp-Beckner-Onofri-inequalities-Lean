import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0196
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0196
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1568 : minorantGammaCheck GammaPanel1568.certificate 1326=true := by decide +kernel
noncomputable def cell1568 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1568.certificate 1326 accepted1568
theorem accepted1569 : minorantGammaCheck GammaPanel1569.certificate 1327=true := by decide +kernel
noncomputable def cell1569 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1569.certificate 1327 accepted1569
theorem accepted1570 : minorantGammaCheck GammaPanel1570.certificate 1328=true := by decide +kernel
noncomputable def cell1570 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1570.certificate 1328 accepted1570
theorem accepted1571 : minorantGammaCheck GammaPanel1571.certificate 1329=true := by decide +kernel
noncomputable def cell1571 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1571.certificate 1329 accepted1571
theorem accepted1572 : minorantGammaCheck GammaPanel1572.certificate 1330=true := by decide +kernel
noncomputable def cell1572 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1572.certificate 1330 accepted1572
theorem accepted1573 : minorantGammaCheck GammaPanel1573.certificate 1331=true := by decide +kernel
noncomputable def cell1573 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1573.certificate 1331 accepted1573
theorem accepted1574 : minorantGammaCheck GammaPanel1574.certificate 1332=true := by decide +kernel
noncomputable def cell1574 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1574.certificate 1332 accepted1574
theorem accepted1575 : minorantGammaCheck GammaPanel1575.certificate 1333=true := by decide +kernel
noncomputable def cell1575 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1575.certificate 1333 accepted1575
noncomputable def cells : List CertifiedMinorantCell := [cell1568, cell1569, cell1570, cell1571, cell1572, cell1573, cell1574, cell1575]
theorem chainAccepted : minorantChainCheck (849/1000) (4249/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (849/1000) (4249/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0196
