module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0090

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0090
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0720 : minorantGammaCheck GammaPanel0720.certificate 618=true := by decide +kernel
noncomputable def cell0720 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0720.certificate 618 accepted0720
theorem accepted0721 : minorantGammaCheck GammaPanel0721.certificate 619=true := by decide +kernel
noncomputable def cell0721 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0721.certificate 619 accepted0721
theorem accepted0722 : minorantGammaCheck GammaPanel0722.certificate 620=true := by decide +kernel
noncomputable def cell0722 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0722.certificate 620 accepted0722
theorem accepted0723 : minorantGammaCheck GammaPanel0723.certificate 621=true := by decide +kernel
noncomputable def cell0723 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0723.certificate 621 accepted0723
theorem accepted0724 : minorantGammaCheck GammaPanel0724.certificate 622=true := by decide +kernel
noncomputable def cell0724 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0724.certificate 622 accepted0724
theorem accepted0725 : minorantGammaCheck GammaPanel0725.certificate 623=true := by decide +kernel
noncomputable def cell0725 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0725.certificate 623 accepted0725
theorem accepted0726 : minorantGammaCheck GammaPanel0726.certificate 624=true := by decide +kernel
noncomputable def cell0726 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0726.certificate 624 accepted0726
theorem accepted0727 : minorantGammaCheck GammaPanel0727.certificate 625=true := by decide +kernel
noncomputable def cell0727 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0727.certificate 625 accepted0727
noncomputable def cells : List CertifiedMinorantCell := [cell0720, cell0721, cell0722, cell0723, cell0724, cell0725, cell0726, cell0727]
theorem chainAccepted : minorantChainCheck (101/500) (21/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (101/500) (21/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0090
