import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0162
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0162
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1296 : minorantGammaCheck GammaPanel1296.certificate 1194=true := by decide +kernel
noncomputable def cell1296 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1296.certificate 1194 accepted1296
theorem accepted1297 : minorantGammaCheck GammaPanel1297.certificate 1195=true := by decide +kernel
noncomputable def cell1297 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1297.certificate 1195 accepted1297
theorem accepted1298 : minorantGammaCheck GammaPanel1298.certificate 1196=true := by decide +kernel
noncomputable def cell1298 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1298.certificate 1196 accepted1298
theorem accepted1299 : minorantGammaCheck GammaPanel1299.certificate 1197=true := by decide +kernel
noncomputable def cell1299 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1299.certificate 1197 accepted1299
theorem accepted1300 : minorantGammaCheck GammaPanel1300.certificate 1198=true := by decide +kernel
noncomputable def cell1300 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1300.certificate 1198 accepted1300
theorem accepted1301 : minorantGammaCheck GammaPanel1301.certificate 1199=true := by decide +kernel
noncomputable def cell1301 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1301.certificate 1199 accepted1301
theorem accepted1302 : minorantGammaCheck GammaPanel1302.certificate 1200=true := by decide +kernel
noncomputable def cell1302 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1302.certificate 1200 accepted1302
theorem accepted1303 : minorantGammaCheck GammaPanel1303.certificate 1201=true := by decide +kernel
noncomputable def cell1303 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1303.certificate 1201 accepted1303
noncomputable def cells : List CertifiedMinorantCell := [cell1296, cell1297, cell1298, cell1299, cell1300, cell1301, cell1302, cell1303]
theorem chainAccepted : minorantChainCheck (389/500) (393/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (389/500) (393/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0162
