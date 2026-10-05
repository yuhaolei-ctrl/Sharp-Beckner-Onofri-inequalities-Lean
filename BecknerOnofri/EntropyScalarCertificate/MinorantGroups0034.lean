import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0034
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0034
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0272 : minorantGammaCheck GammaPanel0272.certificate 232=true := by decide +kernel
noncomputable def cell0272 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0272.certificate 232 accepted0272
theorem accepted0273 : minorantGammaCheck GammaPanel0273.certificate 233=true := by decide +kernel
noncomputable def cell0273 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0273.certificate 233 accepted0273
theorem accepted0274 : minorantGammaCheck GammaPanel0274.certificate 234=true := by decide +kernel
noncomputable def cell0274 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0274.certificate 234 accepted0274
theorem accepted0275 : minorantGammaCheck GammaPanel0275.certificate 235=true := by decide +kernel
noncomputable def cell0275 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0275.certificate 235 accepted0275
theorem accepted0276 : minorantGammaCheck GammaPanel0276.certificate 236=true := by decide +kernel
noncomputable def cell0276 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0276.certificate 236 accepted0276
theorem accepted0277 : minorantGammaCheck GammaPanel0277.certificate 237=true := by decide +kernel
noncomputable def cell0277 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0277.certificate 237 accepted0277
theorem accepted0278 : minorantGammaCheck GammaPanel0278.certificate 238=true := by decide +kernel
noncomputable def cell0278 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0278.certificate 238 accepted0278
theorem accepted0279 : minorantGammaCheck GammaPanel0279.certificate 239=true := by decide +kernel
noncomputable def cell0279 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0279.certificate 239 accepted0279
noncomputable def cells : List CertifiedMinorantCell := [cell0272, cell0273, cell0274, cell0275, cell0276, cell0277, cell0278, cell0279]
theorem chainAccepted : minorantChainCheck (1109/10000) (9/80) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1109/10000) (9/80) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0034
