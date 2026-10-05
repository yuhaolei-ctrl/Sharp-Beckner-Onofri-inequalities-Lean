import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0197
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0197
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1576 : minorantGammaCheck GammaPanel1576.certificate 1334=true := by decide +kernel
noncomputable def cell1576 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1576.certificate 1334 accepted1576
theorem accepted1577 : minorantGammaCheck GammaPanel1577.certificate 1335=true := by decide +kernel
noncomputable def cell1577 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1577.certificate 1335 accepted1577
theorem accepted1578 : minorantGammaCheck GammaPanel1578.certificate 1336=true := by decide +kernel
noncomputable def cell1578 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1578.certificate 1336 accepted1578
theorem accepted1579 : minorantGammaCheck GammaPanel1579.certificate 1337=true := by decide +kernel
noncomputable def cell1579 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1579.certificate 1337 accepted1579
theorem accepted1580 : minorantGammaCheck GammaPanel1580.certificate 1338=true := by decide +kernel
noncomputable def cell1580 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1580.certificate 1338 accepted1580
theorem accepted1581 : minorantGammaCheck GammaPanel1581.certificate 1339=true := by decide +kernel
noncomputable def cell1581 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1581.certificate 1339 accepted1581
theorem accepted1582 : minorantGammaCheck GammaPanel1582.certificate 1340=true := by decide +kernel
noncomputable def cell1582 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1582.certificate 1340 accepted1582
theorem accepted1583 : minorantGammaCheck GammaPanel1583.certificate 1341=true := by decide +kernel
noncomputable def cell1583 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1583.certificate 1341 accepted1583
noncomputable def cells : List CertifiedMinorantCell := [cell1576, cell1577, cell1578, cell1579, cell1580, cell1581, cell1582, cell1583]
theorem chainAccepted : minorantChainCheck (4249/5000) (4253/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4249/5000) (4253/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0197
