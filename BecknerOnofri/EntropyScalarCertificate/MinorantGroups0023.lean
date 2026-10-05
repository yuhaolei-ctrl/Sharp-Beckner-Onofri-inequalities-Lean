import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0023
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0023
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0184 : minorantGammaCheck GammaPanel0184.certificate 144=true := by decide +kernel
noncomputable def cell0184 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0184.certificate 144 accepted0184
theorem accepted0185 : minorantGammaCheck GammaPanel0185.certificate 145=true := by decide +kernel
noncomputable def cell0185 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0185.certificate 145 accepted0185
theorem accepted0186 : minorantGammaCheck GammaPanel0186.certificate 146=true := by decide +kernel
noncomputable def cell0186 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0186.certificate 146 accepted0186
theorem accepted0187 : minorantGammaCheck GammaPanel0187.certificate 147=true := by decide +kernel
noncomputable def cell0187 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0187.certificate 147 accepted0187
theorem accepted0188 : minorantGammaCheck GammaPanel0188.certificate 148=true := by decide +kernel
noncomputable def cell0188 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0188.certificate 148 accepted0188
theorem accepted0189 : minorantGammaCheck GammaPanel0189.certificate 149=true := by decide +kernel
noncomputable def cell0189 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0189.certificate 149 accepted0189
theorem accepted0190 : minorantGammaCheck GammaPanel0190.certificate 150=true := by decide +kernel
noncomputable def cell0190 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0190.certificate 150 accepted0190
theorem accepted0191 : minorantGammaCheck GammaPanel0191.certificate 151=true := by decide +kernel
noncomputable def cell0191 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0191.certificate 151 accepted0191
noncomputable def cells : List CertifiedMinorantCell := [cell0184, cell0185, cell0186, cell0187, cell0188, cell0189, cell0190, cell0191]
theorem chainAccepted : minorantChainCheck (933/10000) (949/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (933/10000) (949/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0023
