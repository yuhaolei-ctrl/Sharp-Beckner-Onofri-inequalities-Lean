import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0014
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0014
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0112 : minorantGammaCheck GammaPanel0112.certificate 72=true := by decide +kernel
noncomputable def cell0112 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0112.certificate 72 accepted0112
theorem accepted0113 : minorantGammaCheck GammaPanel0113.certificate 73=true := by decide +kernel
noncomputable def cell0113 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0113.certificate 73 accepted0113
theorem accepted0114 : minorantGammaCheck GammaPanel0114.certificate 74=true := by decide +kernel
noncomputable def cell0114 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0114.certificate 74 accepted0114
theorem accepted0115 : minorantGammaCheck GammaPanel0115.certificate 75=true := by decide +kernel
noncomputable def cell0115 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0115.certificate 75 accepted0115
theorem accepted0116 : minorantGammaCheck GammaPanel0116.certificate 76=true := by decide +kernel
noncomputable def cell0116 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0116.certificate 76 accepted0116
theorem accepted0117 : minorantGammaCheck GammaPanel0117.certificate 77=true := by decide +kernel
noncomputable def cell0117 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0117.certificate 77 accepted0117
theorem accepted0118 : minorantGammaCheck GammaPanel0118.certificate 78=true := by decide +kernel
noncomputable def cell0118 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0118.certificate 78 accepted0118
theorem accepted0119 : minorantGammaCheck GammaPanel0119.certificate 79=true := by decide +kernel
noncomputable def cell0119 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0119.certificate 79 accepted0119
noncomputable def cells : List CertifiedMinorantCell := [cell0112, cell0113, cell0114, cell0115, cell0116, cell0117, cell0118, cell0119]
theorem chainAccepted : minorantChainCheck (789/10000) (161/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (789/10000) (161/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0014
