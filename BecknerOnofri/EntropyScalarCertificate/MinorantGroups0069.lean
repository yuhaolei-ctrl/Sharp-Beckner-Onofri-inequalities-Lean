module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0069

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0069
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0552 : minorantGammaCheck GammaPanel0552.certificate 512=true := by decide +kernel
noncomputable def cell0552 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0552.certificate 512 accepted0552
theorem accepted0553 : minorantGammaCheck GammaPanel0553.certificate 513=true := by decide +kernel
noncomputable def cell0553 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0553.certificate 513 accepted0553
theorem accepted0554 : minorantGammaCheck GammaPanel0554.certificate 514=true := by decide +kernel
noncomputable def cell0554 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0554.certificate 514 accepted0554
theorem accepted0555 : minorantGammaCheck GammaPanel0555.certificate 515=true := by decide +kernel
noncomputable def cell0555 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0555.certificate 515 accepted0555
theorem accepted0556 : minorantGammaCheck GammaPanel0556.certificate 516=true := by decide +kernel
noncomputable def cell0556 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0556.certificate 516 accepted0556
theorem accepted0557 : minorantGammaCheck GammaPanel0557.certificate 517=true := by decide +kernel
noncomputable def cell0557 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0557.certificate 517 accepted0557
theorem accepted0558 : minorantGammaCheck GammaPanel0558.certificate 518=true := by decide +kernel
noncomputable def cell0558 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0558.certificate 518 accepted0558
theorem accepted0559 : minorantGammaCheck GammaPanel0559.certificate 519=true := by decide +kernel
noncomputable def cell0559 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0559.certificate 519 accepted0559
noncomputable def cells : List CertifiedMinorantCell := [cell0552, cell0553, cell0554, cell0555, cell0556, cell0557, cell0558, cell0559]
theorem chainAccepted : minorantChainCheck (1669/10000) (337/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1669/10000) (337/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0069
