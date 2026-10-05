import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0016
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0016
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0128 : minorantGammaCheck GammaPanel0128.certificate 88=true := by decide +kernel
noncomputable def cell0128 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0128.certificate 88 accepted0128
theorem accepted0129 : minorantGammaCheck GammaPanel0129.certificate 89=true := by decide +kernel
noncomputable def cell0129 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0129.certificate 89 accepted0129
theorem accepted0130 : minorantGammaCheck GammaPanel0130.certificate 90=true := by decide +kernel
noncomputable def cell0130 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0130.certificate 90 accepted0130
theorem accepted0131 : minorantGammaCheck GammaPanel0131.certificate 91=true := by decide +kernel
noncomputable def cell0131 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0131.certificate 91 accepted0131
theorem accepted0132 : minorantGammaCheck GammaPanel0132.certificate 92=true := by decide +kernel
noncomputable def cell0132 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0132.certificate 92 accepted0132
theorem accepted0133 : minorantGammaCheck GammaPanel0133.certificate 93=true := by decide +kernel
noncomputable def cell0133 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0133.certificate 93 accepted0133
theorem accepted0134 : minorantGammaCheck GammaPanel0134.certificate 94=true := by decide +kernel
noncomputable def cell0134 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0134.certificate 94 accepted0134
theorem accepted0135 : minorantGammaCheck GammaPanel0135.certificate 95=true := by decide +kernel
noncomputable def cell0135 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0135.certificate 95 accepted0135
noncomputable def cells : List CertifiedMinorantCell := [cell0128, cell0129, cell0130, cell0131, cell0132, cell0133, cell0134, cell0135]
theorem chainAccepted : minorantChainCheck (821/10000) (837/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (821/10000) (837/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0016
