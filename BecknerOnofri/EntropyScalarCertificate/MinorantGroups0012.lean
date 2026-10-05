import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0012
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0012
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0096 : minorantGammaCheck GammaPanel0096.certificate 56=true := by decide +kernel
noncomputable def cell0096 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0096.certificate 56 accepted0096
theorem accepted0097 : minorantGammaCheck GammaPanel0097.certificate 57=true := by decide +kernel
noncomputable def cell0097 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0097.certificate 57 accepted0097
theorem accepted0098 : minorantGammaCheck GammaPanel0098.certificate 58=true := by decide +kernel
noncomputable def cell0098 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0098.certificate 58 accepted0098
theorem accepted0099 : minorantGammaCheck GammaPanel0099.certificate 59=true := by decide +kernel
noncomputable def cell0099 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0099.certificate 59 accepted0099
theorem accepted0100 : minorantGammaCheck GammaPanel0100.certificate 60=true := by decide +kernel
noncomputable def cell0100 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0100.certificate 60 accepted0100
theorem accepted0101 : minorantGammaCheck GammaPanel0101.certificate 61=true := by decide +kernel
noncomputable def cell0101 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0101.certificate 61 accepted0101
theorem accepted0102 : minorantGammaCheck GammaPanel0102.certificate 62=true := by decide +kernel
noncomputable def cell0102 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0102.certificate 62 accepted0102
theorem accepted0103 : minorantGammaCheck GammaPanel0103.certificate 63=true := by decide +kernel
noncomputable def cell0103 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0103.certificate 63 accepted0103
noncomputable def cells : List CertifiedMinorantCell := [cell0096, cell0097, cell0098, cell0099, cell0100, cell0101, cell0102, cell0103]
theorem chainAccepted : minorantChainCheck (757/10000) (773/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (757/10000) (773/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0012
