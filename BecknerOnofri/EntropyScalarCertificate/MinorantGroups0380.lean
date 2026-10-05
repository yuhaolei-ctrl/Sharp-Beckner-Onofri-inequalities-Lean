import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0380
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0380
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3040 : minorantGammaCheck GammaPanel3040.certificate 1621=true := by decide +kernel
noncomputable def cell3040 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3040.certificate 1621 accepted3040
theorem accepted3041 : minorantGammaCheck GammaPanel3041.certificate 1621=true := by decide +kernel
noncomputable def cell3041 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3041.certificate 1621 accepted3041
theorem accepted3042 : minorantGammaCheck GammaPanel3042.certificate 1621=true := by decide +kernel
noncomputable def cell3042 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3042.certificate 1621 accepted3042
theorem accepted3043 : minorantGammaCheck GammaPanel3043.certificate 1621=true := by decide +kernel
noncomputable def cell3043 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3043.certificate 1621 accepted3043
theorem accepted3044 : minorantGammaCheck GammaPanel3044.certificate 1621=true := by decide +kernel
noncomputable def cell3044 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3044.certificate 1621 accepted3044
theorem accepted3045 : minorantGammaCheck GammaPanel3045.certificate 1621=true := by decide +kernel
noncomputable def cell3045 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3045.certificate 1621 accepted3045
theorem accepted3046 : minorantGammaCheck GammaPanel3046.certificate 1621=true := by decide +kernel
noncomputable def cell3046 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3046.certificate 1621 accepted3046
theorem accepted3047 : minorantGammaCheck GammaPanel3047.certificate 1621=true := by decide +kernel
noncomputable def cell3047 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3047.certificate 1621 accepted3047
noncomputable def cells : List CertifiedMinorantCell := [cell3040, cell3041, cell3042, cell3043, cell3044, cell3045, cell3046, cell3047]
theorem chainAccepted : minorantChainCheck (6241/6250) (4993/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (6241/6250) (4993/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0380
