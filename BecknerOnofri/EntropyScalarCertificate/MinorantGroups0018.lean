import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0018
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0018
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0144 : minorantGammaCheck GammaPanel0144.certificate 104=true := by decide +kernel
noncomputable def cell0144 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0144.certificate 104 accepted0144
theorem accepted0145 : minorantGammaCheck GammaPanel0145.certificate 105=true := by decide +kernel
noncomputable def cell0145 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0145.certificate 105 accepted0145
theorem accepted0146 : minorantGammaCheck GammaPanel0146.certificate 106=true := by decide +kernel
noncomputable def cell0146 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0146.certificate 106 accepted0146
theorem accepted0147 : minorantGammaCheck GammaPanel0147.certificate 107=true := by decide +kernel
noncomputable def cell0147 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0147.certificate 107 accepted0147
theorem accepted0148 : minorantGammaCheck GammaPanel0148.certificate 108=true := by decide +kernel
noncomputable def cell0148 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0148.certificate 108 accepted0148
theorem accepted0149 : minorantGammaCheck GammaPanel0149.certificate 109=true := by decide +kernel
noncomputable def cell0149 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0149.certificate 109 accepted0149
theorem accepted0150 : minorantGammaCheck GammaPanel0150.certificate 110=true := by decide +kernel
noncomputable def cell0150 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0150.certificate 110 accepted0150
theorem accepted0151 : minorantGammaCheck GammaPanel0151.certificate 111=true := by decide +kernel
noncomputable def cell0151 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0151.certificate 111 accepted0151
noncomputable def cells : List CertifiedMinorantCell := [cell0144, cell0145, cell0146, cell0147, cell0148, cell0149, cell0150, cell0151]
theorem chainAccepted : minorantChainCheck (853/10000) (869/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (853/10000) (869/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0018
