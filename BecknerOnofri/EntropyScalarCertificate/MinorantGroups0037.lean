module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0037

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0037
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0296 : minorantGammaCheck GammaPanel0296.certificate 256=true := by decide +kernel
noncomputable def cell0296 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0296.certificate 256 accepted0296
theorem accepted0297 : minorantGammaCheck GammaPanel0297.certificate 257=true := by decide +kernel
noncomputable def cell0297 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0297.certificate 257 accepted0297
theorem accepted0298 : minorantGammaCheck GammaPanel0298.certificate 258=true := by decide +kernel
noncomputable def cell0298 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0298.certificate 258 accepted0298
theorem accepted0299 : minorantGammaCheck GammaPanel0299.certificate 259=true := by decide +kernel
noncomputable def cell0299 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0299.certificate 259 accepted0299
theorem accepted0300 : minorantGammaCheck GammaPanel0300.certificate 260=true := by decide +kernel
noncomputable def cell0300 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0300.certificate 260 accepted0300
theorem accepted0301 : minorantGammaCheck GammaPanel0301.certificate 261=true := by decide +kernel
noncomputable def cell0301 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0301.certificate 261 accepted0301
theorem accepted0302 : minorantGammaCheck GammaPanel0302.certificate 262=true := by decide +kernel
noncomputable def cell0302 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0302.certificate 262 accepted0302
theorem accepted0303 : minorantGammaCheck GammaPanel0303.certificate 263=true := by decide +kernel
noncomputable def cell0303 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0303.certificate 263 accepted0303
noncomputable def cells : List CertifiedMinorantCell := [cell0296, cell0297, cell0298, cell0299, cell0300, cell0301, cell0302, cell0303]
theorem chainAccepted : minorantChainCheck (1157/10000) (1173/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1157/10000) (1173/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0037
