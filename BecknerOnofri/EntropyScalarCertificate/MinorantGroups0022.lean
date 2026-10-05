import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0022
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0022
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0176 : minorantGammaCheck GammaPanel0176.certificate 136=true := by decide +kernel
noncomputable def cell0176 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0176.certificate 136 accepted0176
theorem accepted0177 : minorantGammaCheck GammaPanel0177.certificate 137=true := by decide +kernel
noncomputable def cell0177 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0177.certificate 137 accepted0177
theorem accepted0178 : minorantGammaCheck GammaPanel0178.certificate 138=true := by decide +kernel
noncomputable def cell0178 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0178.certificate 138 accepted0178
theorem accepted0179 : minorantGammaCheck GammaPanel0179.certificate 139=true := by decide +kernel
noncomputable def cell0179 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0179.certificate 139 accepted0179
theorem accepted0180 : minorantGammaCheck GammaPanel0180.certificate 140=true := by decide +kernel
noncomputable def cell0180 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0180.certificate 140 accepted0180
theorem accepted0181 : minorantGammaCheck GammaPanel0181.certificate 141=true := by decide +kernel
noncomputable def cell0181 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0181.certificate 141 accepted0181
theorem accepted0182 : minorantGammaCheck GammaPanel0182.certificate 142=true := by decide +kernel
noncomputable def cell0182 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0182.certificate 142 accepted0182
theorem accepted0183 : minorantGammaCheck GammaPanel0183.certificate 143=true := by decide +kernel
noncomputable def cell0183 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0183.certificate 143 accepted0183
noncomputable def cells : List CertifiedMinorantCell := [cell0176, cell0177, cell0178, cell0179, cell0180, cell0181, cell0182, cell0183]
theorem chainAccepted : minorantChainCheck (917/10000) (933/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (917/10000) (933/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0022
