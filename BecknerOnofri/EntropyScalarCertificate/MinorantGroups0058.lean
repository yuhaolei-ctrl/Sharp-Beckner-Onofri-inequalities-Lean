module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0058

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0058
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0464 : minorantGammaCheck GammaPanel0464.certificate 424=true := by decide +kernel
noncomputable def cell0464 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0464.certificate 424 accepted0464
theorem accepted0465 : minorantGammaCheck GammaPanel0465.certificate 425=true := by decide +kernel
noncomputable def cell0465 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0465.certificate 425 accepted0465
theorem accepted0466 : minorantGammaCheck GammaPanel0466.certificate 426=true := by decide +kernel
noncomputable def cell0466 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0466.certificate 426 accepted0466
theorem accepted0467 : minorantGammaCheck GammaPanel0467.certificate 427=true := by decide +kernel
noncomputable def cell0467 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0467.certificate 427 accepted0467
theorem accepted0468 : minorantGammaCheck GammaPanel0468.certificate 428=true := by decide +kernel
noncomputable def cell0468 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0468.certificate 428 accepted0468
theorem accepted0469 : minorantGammaCheck GammaPanel0469.certificate 429=true := by decide +kernel
noncomputable def cell0469 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0469.certificate 429 accepted0469
theorem accepted0470 : minorantGammaCheck GammaPanel0470.certificate 430=true := by decide +kernel
noncomputable def cell0470 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0470.certificate 430 accepted0470
theorem accepted0471 : minorantGammaCheck GammaPanel0471.certificate 431=true := by decide +kernel
noncomputable def cell0471 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0471.certificate 431 accepted0471
noncomputable def cells : List CertifiedMinorantCell := [cell0464, cell0465, cell0466, cell0467, cell0468, cell0469, cell0470, cell0471]
theorem chainAccepted : minorantChainCheck (1493/10000) (1509/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1493/10000) (1509/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0058
