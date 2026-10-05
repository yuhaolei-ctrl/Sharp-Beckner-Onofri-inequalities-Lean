module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0040

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0040
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0320 : minorantGammaCheck GammaPanel0320.certificate 280=true := by decide +kernel
noncomputable def cell0320 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0320.certificate 280 accepted0320
theorem accepted0321 : minorantGammaCheck GammaPanel0321.certificate 281=true := by decide +kernel
noncomputable def cell0321 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0321.certificate 281 accepted0321
theorem accepted0322 : minorantGammaCheck GammaPanel0322.certificate 282=true := by decide +kernel
noncomputable def cell0322 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0322.certificate 282 accepted0322
theorem accepted0323 : minorantGammaCheck GammaPanel0323.certificate 283=true := by decide +kernel
noncomputable def cell0323 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0323.certificate 283 accepted0323
theorem accepted0324 : minorantGammaCheck GammaPanel0324.certificate 284=true := by decide +kernel
noncomputable def cell0324 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0324.certificate 284 accepted0324
theorem accepted0325 : minorantGammaCheck GammaPanel0325.certificate 285=true := by decide +kernel
noncomputable def cell0325 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0325.certificate 285 accepted0325
theorem accepted0326 : minorantGammaCheck GammaPanel0326.certificate 286=true := by decide +kernel
noncomputable def cell0326 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0326.certificate 286 accepted0326
theorem accepted0327 : minorantGammaCheck GammaPanel0327.certificate 287=true := by decide +kernel
noncomputable def cell0327 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0327.certificate 287 accepted0327
noncomputable def cells : List CertifiedMinorantCell := [cell0320, cell0321, cell0322, cell0323, cell0324, cell0325, cell0326, cell0327]
theorem chainAccepted : minorantChainCheck (241/2000) (1221/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (241/2000) (1221/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0040
