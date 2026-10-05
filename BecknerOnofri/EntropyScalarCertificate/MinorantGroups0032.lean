module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0032

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0032
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0256 : minorantGammaCheck GammaPanel0256.certificate 216=true := by decide +kernel
noncomputable def cell0256 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0256.certificate 216 accepted0256
theorem accepted0257 : minorantGammaCheck GammaPanel0257.certificate 217=true := by decide +kernel
noncomputable def cell0257 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0257.certificate 217 accepted0257
theorem accepted0258 : minorantGammaCheck GammaPanel0258.certificate 218=true := by decide +kernel
noncomputable def cell0258 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0258.certificate 218 accepted0258
theorem accepted0259 : minorantGammaCheck GammaPanel0259.certificate 219=true := by decide +kernel
noncomputable def cell0259 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0259.certificate 219 accepted0259
theorem accepted0260 : minorantGammaCheck GammaPanel0260.certificate 220=true := by decide +kernel
noncomputable def cell0260 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0260.certificate 220 accepted0260
theorem accepted0261 : minorantGammaCheck GammaPanel0261.certificate 221=true := by decide +kernel
noncomputable def cell0261 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0261.certificate 221 accepted0261
theorem accepted0262 : minorantGammaCheck GammaPanel0262.certificate 222=true := by decide +kernel
noncomputable def cell0262 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0262.certificate 222 accepted0262
theorem accepted0263 : minorantGammaCheck GammaPanel0263.certificate 223=true := by decide +kernel
noncomputable def cell0263 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0263.certificate 223 accepted0263
noncomputable def cells : List CertifiedMinorantCell := [cell0256, cell0257, cell0258, cell0259, cell0260, cell0261, cell0262, cell0263]
theorem chainAccepted : minorantChainCheck (1077/10000) (1093/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1077/10000) (1093/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0032
