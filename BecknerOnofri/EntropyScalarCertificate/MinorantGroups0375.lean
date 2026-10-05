import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0375
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0375
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3000 : minorantGammaCheck GammaPanel3000.certificate 1621=true := by decide +kernel
noncomputable def cell3000 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3000.certificate 1621 accepted3000
theorem accepted3001 : minorantGammaCheck GammaPanel3001.certificate 1621=true := by decide +kernel
noncomputable def cell3001 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3001.certificate 1621 accepted3001
theorem accepted3002 : minorantGammaCheck GammaPanel3002.certificate 1621=true := by decide +kernel
noncomputable def cell3002 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3002.certificate 1621 accepted3002
theorem accepted3003 : minorantGammaCheck GammaPanel3003.certificate 1621=true := by decide +kernel
noncomputable def cell3003 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3003.certificate 1621 accepted3003
theorem accepted3004 : minorantGammaCheck GammaPanel3004.certificate 1621=true := by decide +kernel
noncomputable def cell3004 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3004.certificate 1621 accepted3004
theorem accepted3005 : minorantGammaCheck GammaPanel3005.certificate 1621=true := by decide +kernel
noncomputable def cell3005 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3005.certificate 1621 accepted3005
theorem accepted3006 : minorantGammaCheck GammaPanel3006.certificate 1621=true := by decide +kernel
noncomputable def cell3006 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3006.certificate 1621 accepted3006
theorem accepted3007 : minorantGammaCheck GammaPanel3007.certificate 1621=true := by decide +kernel
noncomputable def cell3007 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3007.certificate 1621 accepted3007
noncomputable def cells : List CertifiedMinorantCell := [cell3000, cell3001, cell3002, cell3003, cell3004, cell3005, cell3006, cell3007]
theorem chainAccepted : minorantChainCheck (24959/25000) (624/625) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24959/25000) (624/625) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0375
