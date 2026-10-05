module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0027

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0027
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0216 : minorantGammaCheck GammaPanel0216.certificate 176=true := by decide +kernel
noncomputable def cell0216 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0216.certificate 176 accepted0216
theorem accepted0217 : minorantGammaCheck GammaPanel0217.certificate 177=true := by decide +kernel
noncomputable def cell0217 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0217.certificate 177 accepted0217
theorem accepted0218 : minorantGammaCheck GammaPanel0218.certificate 178=true := by decide +kernel
noncomputable def cell0218 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0218.certificate 178 accepted0218
theorem accepted0219 : minorantGammaCheck GammaPanel0219.certificate 179=true := by decide +kernel
noncomputable def cell0219 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0219.certificate 179 accepted0219
theorem accepted0220 : minorantGammaCheck GammaPanel0220.certificate 180=true := by decide +kernel
noncomputable def cell0220 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0220.certificate 180 accepted0220
theorem accepted0221 : minorantGammaCheck GammaPanel0221.certificate 181=true := by decide +kernel
noncomputable def cell0221 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0221.certificate 181 accepted0221
theorem accepted0222 : minorantGammaCheck GammaPanel0222.certificate 182=true := by decide +kernel
noncomputable def cell0222 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0222.certificate 182 accepted0222
theorem accepted0223 : minorantGammaCheck GammaPanel0223.certificate 183=true := by decide +kernel
noncomputable def cell0223 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0223.certificate 183 accepted0223
noncomputable def cells : List CertifiedMinorantCell := [cell0216, cell0217, cell0218, cell0219, cell0220, cell0221, cell0222, cell0223]
theorem chainAccepted : minorantChainCheck (997/10000) (1013/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (997/10000) (1013/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0027
