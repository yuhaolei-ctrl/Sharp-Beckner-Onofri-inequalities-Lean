import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0209
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0209
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1672 : minorantGammaCheck GammaPanel1672.certificate 1430=true := by decide +kernel
noncomputable def cell1672 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1672.certificate 1430 accepted1672
theorem accepted1673 : minorantGammaCheck GammaPanel1673.certificate 1431=true := by decide +kernel
noncomputable def cell1673 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1673.certificate 1431 accepted1673
theorem accepted1674 : minorantGammaCheck GammaPanel1674.certificate 1432=true := by decide +kernel
noncomputable def cell1674 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1674.certificate 1432 accepted1674
theorem accepted1675 : minorantGammaCheck GammaPanel1675.certificate 1433=true := by decide +kernel
noncomputable def cell1675 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1675.certificate 1433 accepted1675
theorem accepted1676 : minorantGammaCheck GammaPanel1676.certificate 1434=true := by decide +kernel
noncomputable def cell1676 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1676.certificate 1434 accepted1676
theorem accepted1677 : minorantGammaCheck GammaPanel1677.certificate 1435=true := by decide +kernel
noncomputable def cell1677 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1677.certificate 1435 accepted1677
theorem accepted1678 : minorantGammaCheck GammaPanel1678.certificate 1436=true := by decide +kernel
noncomputable def cell1678 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1678.certificate 1436 accepted1678
theorem accepted1679 : minorantGammaCheck GammaPanel1679.certificate 1437=true := by decide +kernel
noncomputable def cell1679 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1679.certificate 1437 accepted1679
noncomputable def cells : List CertifiedMinorantCell := [cell1672, cell1673, cell1674, cell1675, cell1676, cell1677, cell1678, cell1679]
theorem chainAccepted : minorantChainCheck (4297/5000) (4301/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4297/5000) (4301/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0209
