import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0376
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0376
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3008 : minorantGammaCheck GammaPanel3008.certificate 1621=true := by decide +kernel
noncomputable def cell3008 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3008.certificate 1621 accepted3008
theorem accepted3009 : minorantGammaCheck GammaPanel3009.certificate 1621=true := by decide +kernel
noncomputable def cell3009 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3009.certificate 1621 accepted3009
theorem accepted3010 : minorantGammaCheck GammaPanel3010.certificate 1621=true := by decide +kernel
noncomputable def cell3010 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3010.certificate 1621 accepted3010
theorem accepted3011 : minorantGammaCheck GammaPanel3011.certificate 1621=true := by decide +kernel
noncomputable def cell3011 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3011.certificate 1621 accepted3011
theorem accepted3012 : minorantGammaCheck GammaPanel3012.certificate 1621=true := by decide +kernel
noncomputable def cell3012 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3012.certificate 1621 accepted3012
theorem accepted3013 : minorantGammaCheck GammaPanel3013.certificate 1621=true := by decide +kernel
noncomputable def cell3013 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3013.certificate 1621 accepted3013
theorem accepted3014 : minorantGammaCheck GammaPanel3014.certificate 1621=true := by decide +kernel
noncomputable def cell3014 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3014.certificate 1621 accepted3014
theorem accepted3015 : minorantGammaCheck GammaPanel3015.certificate 1621=true := by decide +kernel
noncomputable def cell3015 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3015.certificate 1621 accepted3015
noncomputable def cells : List CertifiedMinorantCell := [cell3008, cell3009, cell3010, cell3011, cell3012, cell3013, cell3014, cell3015]
theorem chainAccepted : minorantChainCheck (624/625) (24961/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (624/625) (24961/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0376
