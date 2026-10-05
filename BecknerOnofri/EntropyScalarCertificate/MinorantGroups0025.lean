import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0025
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0025
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0200 : minorantGammaCheck GammaPanel0200.certificate 160=true := by decide +kernel
noncomputable def cell0200 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0200.certificate 160 accepted0200
theorem accepted0201 : minorantGammaCheck GammaPanel0201.certificate 161=true := by decide +kernel
noncomputable def cell0201 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0201.certificate 161 accepted0201
theorem accepted0202 : minorantGammaCheck GammaPanel0202.certificate 162=true := by decide +kernel
noncomputable def cell0202 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0202.certificate 162 accepted0202
theorem accepted0203 : minorantGammaCheck GammaPanel0203.certificate 163=true := by decide +kernel
noncomputable def cell0203 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0203.certificate 163 accepted0203
theorem accepted0204 : minorantGammaCheck GammaPanel0204.certificate 164=true := by decide +kernel
noncomputable def cell0204 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0204.certificate 164 accepted0204
theorem accepted0205 : minorantGammaCheck GammaPanel0205.certificate 165=true := by decide +kernel
noncomputable def cell0205 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0205.certificate 165 accepted0205
theorem accepted0206 : minorantGammaCheck GammaPanel0206.certificate 166=true := by decide +kernel
noncomputable def cell0206 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0206.certificate 166 accepted0206
theorem accepted0207 : minorantGammaCheck GammaPanel0207.certificate 167=true := by decide +kernel
noncomputable def cell0207 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0207.certificate 167 accepted0207
noncomputable def cells : List CertifiedMinorantCell := [cell0200, cell0201, cell0202, cell0203, cell0204, cell0205, cell0206, cell0207]
theorem chainAccepted : minorantChainCheck (193/2000) (981/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (193/2000) (981/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0025
