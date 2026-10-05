import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0007
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0007
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0056 : minorantGammaCheck GammaPanel0056.certificate 16=true := by decide +kernel
noncomputable def cell0056 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0056.certificate 16 accepted0056
theorem accepted0057 : minorantGammaCheck GammaPanel0057.certificate 17=true := by decide +kernel
noncomputable def cell0057 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0057.certificate 17 accepted0057
theorem accepted0058 : minorantGammaCheck GammaPanel0058.certificate 18=true := by decide +kernel
noncomputable def cell0058 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0058.certificate 18 accepted0058
theorem accepted0059 : minorantGammaCheck GammaPanel0059.certificate 19=true := by decide +kernel
noncomputable def cell0059 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0059.certificate 19 accepted0059
theorem accepted0060 : minorantGammaCheck GammaPanel0060.certificate 20=true := by decide +kernel
noncomputable def cell0060 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0060.certificate 20 accepted0060
theorem accepted0061 : minorantGammaCheck GammaPanel0061.certificate 21=true := by decide +kernel
noncomputable def cell0061 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0061.certificate 21 accepted0061
theorem accepted0062 : minorantGammaCheck GammaPanel0062.certificate 22=true := by decide +kernel
noncomputable def cell0062 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0062.certificate 22 accepted0062
theorem accepted0063 : minorantGammaCheck GammaPanel0063.certificate 23=true := by decide +kernel
noncomputable def cell0063 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0063.certificate 23 accepted0063
noncomputable def cells : List CertifiedMinorantCell := [cell0056, cell0057, cell0058, cell0059, cell0060, cell0061, cell0062, cell0063]
theorem chainAccepted : minorantChainCheck (677/10000) (693/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (677/10000) (693/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0007
