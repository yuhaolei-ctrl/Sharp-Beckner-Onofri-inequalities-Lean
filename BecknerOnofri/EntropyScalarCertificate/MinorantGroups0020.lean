import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0020
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0020
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0160 : minorantGammaCheck GammaPanel0160.certificate 120=true := by decide +kernel
noncomputable def cell0160 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0160.certificate 120 accepted0160
theorem accepted0161 : minorantGammaCheck GammaPanel0161.certificate 121=true := by decide +kernel
noncomputable def cell0161 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0161.certificate 121 accepted0161
theorem accepted0162 : minorantGammaCheck GammaPanel0162.certificate 122=true := by decide +kernel
noncomputable def cell0162 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0162.certificate 122 accepted0162
theorem accepted0163 : minorantGammaCheck GammaPanel0163.certificate 123=true := by decide +kernel
noncomputable def cell0163 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0163.certificate 123 accepted0163
theorem accepted0164 : minorantGammaCheck GammaPanel0164.certificate 124=true := by decide +kernel
noncomputable def cell0164 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0164.certificate 124 accepted0164
theorem accepted0165 : minorantGammaCheck GammaPanel0165.certificate 125=true := by decide +kernel
noncomputable def cell0165 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0165.certificate 125 accepted0165
theorem accepted0166 : minorantGammaCheck GammaPanel0166.certificate 126=true := by decide +kernel
noncomputable def cell0166 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0166.certificate 126 accepted0166
theorem accepted0167 : minorantGammaCheck GammaPanel0167.certificate 127=true := by decide +kernel
noncomputable def cell0167 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0167.certificate 127 accepted0167
noncomputable def cells : List CertifiedMinorantCell := [cell0160, cell0161, cell0162, cell0163, cell0164, cell0165, cell0166, cell0167]
theorem chainAccepted : minorantChainCheck (177/2000) (901/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (177/2000) (901/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0020
