import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0245
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0245
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1960 : minorantGammaCheck GammaPanel1960.certificate 1604=true := by decide +kernel
noncomputable def cell1960 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1960.certificate 1604 accepted1960
theorem accepted1961 : minorantGammaCheck GammaPanel1961.certificate 1605=true := by decide +kernel
noncomputable def cell1961 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1961.certificate 1605 accepted1961
theorem accepted1962 : minorantGammaCheck GammaPanel1962.certificate 1606=true := by decide +kernel
noncomputable def cell1962 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1962.certificate 1606 accepted1962
theorem accepted1963 : minorantGammaCheck GammaPanel1963.certificate 1607=true := by decide +kernel
noncomputable def cell1963 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1963.certificate 1607 accepted1963
theorem accepted1964 : minorantGammaCheck GammaPanel1964.certificate 1608=true := by decide +kernel
noncomputable def cell1964 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1964.certificate 1608 accepted1964
theorem accepted1965 : minorantGammaCheck GammaPanel1965.certificate 1609=true := by decide +kernel
noncomputable def cell1965 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1965.certificate 1609 accepted1965
theorem accepted1966 : minorantGammaCheck GammaPanel1966.certificate 1610=true := by decide +kernel
noncomputable def cell1966 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1966.certificate 1610 accepted1966
theorem accepted1967 : minorantGammaCheck GammaPanel1967.certificate 1611=true := by decide +kernel
noncomputable def cell1967 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1967.certificate 1611 accepted1967
noncomputable def cells : List CertifiedMinorantCell := [cell1960, cell1961, cell1962, cell1963, cell1964, cell1965, cell1966, cell1967]
theorem chainAccepted : minorantChainCheck (941/1000) (189/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (941/1000) (189/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0245
