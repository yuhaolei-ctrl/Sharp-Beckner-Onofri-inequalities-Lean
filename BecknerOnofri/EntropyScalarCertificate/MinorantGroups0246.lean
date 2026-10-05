import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0246
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0246
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1968 : minorantGammaCheck GammaPanel1968.certificate 1612=true := by decide +kernel
noncomputable def cell1968 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1968.certificate 1612 accepted1968
theorem accepted1969 : minorantGammaCheck GammaPanel1969.certificate 1613=true := by decide +kernel
noncomputable def cell1969 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1969.certificate 1613 accepted1969
theorem accepted1970 : minorantGammaCheck GammaPanel1970.certificate 1614=true := by decide +kernel
noncomputable def cell1970 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1970.certificate 1614 accepted1970
theorem accepted1971 : minorantGammaCheck GammaPanel1971.certificate 1615=true := by decide +kernel
noncomputable def cell1971 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1971.certificate 1615 accepted1971
theorem accepted1972 : minorantGammaCheck GammaPanel1972.certificate 1616=true := by decide +kernel
noncomputable def cell1972 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1972.certificate 1616 accepted1972
theorem accepted1973 : minorantGammaCheck GammaPanel1973.certificate 1617=true := by decide +kernel
noncomputable def cell1973 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1973.certificate 1617 accepted1973
theorem accepted1974 : minorantGammaCheck GammaPanel1974.certificate 1618=true := by decide +kernel
noncomputable def cell1974 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1974.certificate 1618 accepted1974
theorem accepted1975 : minorantGammaCheck GammaPanel1975.certificate 1619=true := by decide +kernel
noncomputable def cell1975 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1975.certificate 1619 accepted1975
noncomputable def cells : List CertifiedMinorantCell := [cell1968, cell1969, cell1970, cell1971, cell1972, cell1973, cell1974, cell1975]
theorem chainAccepted : minorantChainCheck (189/200) (949/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (189/200) (949/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0246
