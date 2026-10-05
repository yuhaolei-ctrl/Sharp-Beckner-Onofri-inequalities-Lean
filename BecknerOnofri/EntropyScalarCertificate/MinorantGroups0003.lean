import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0003
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0003
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0024 : minorantGammaCheck GammaPanel0024.certificate 0=true := by decide +kernel
noncomputable def cell0024 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0024.certificate 0 accepted0024
theorem accepted0025 : minorantGammaCheck GammaPanel0025.certificate 0=true := by decide +kernel
noncomputable def cell0025 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0025.certificate 0 accepted0025
theorem accepted0026 : minorantGammaCheck GammaPanel0026.certificate 0=true := by decide +kernel
noncomputable def cell0026 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0026.certificate 0 accepted0026
theorem accepted0027 : minorantGammaCheck GammaPanel0027.certificate 0=true := by decide +kernel
noncomputable def cell0027 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0027.certificate 0 accepted0027
theorem accepted0028 : minorantGammaCheck GammaPanel0028.certificate 0=true := by decide +kernel
noncomputable def cell0028 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0028.certificate 0 accepted0028
theorem accepted0029 : minorantGammaCheck GammaPanel0029.certificate 0=true := by decide +kernel
noncomputable def cell0029 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0029.certificate 0 accepted0029
theorem accepted0030 : minorantGammaCheck GammaPanel0030.certificate 0=true := by decide +kernel
noncomputable def cell0030 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0030.certificate 0 accepted0030
theorem accepted0031 : minorantGammaCheck GammaPanel0031.certificate 0=true := by decide +kernel
noncomputable def cell0031 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0031.certificate 0 accepted0031
noncomputable def cells : List CertifiedMinorantCell := [cell0024, cell0025, cell0026, cell0027, cell0028, cell0029, cell0030, cell0031]
theorem chainAccepted : minorantChainCheck (637/10000) (641/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (637/10000) (641/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0003
