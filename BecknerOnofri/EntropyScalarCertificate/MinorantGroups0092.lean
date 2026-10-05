import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0092
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0092
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0736 : minorantGammaCheck GammaPanel0736.certificate 634=true := by decide +kernel
noncomputable def cell0736 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0736.certificate 634 accepted0736
theorem accepted0737 : minorantGammaCheck GammaPanel0737.certificate 635=true := by decide +kernel
noncomputable def cell0737 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0737.certificate 635 accepted0737
theorem accepted0738 : minorantGammaCheck GammaPanel0738.certificate 636=true := by decide +kernel
noncomputable def cell0738 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0738.certificate 636 accepted0738
theorem accepted0739 : minorantGammaCheck GammaPanel0739.certificate 637=true := by decide +kernel
noncomputable def cell0739 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0739.certificate 637 accepted0739
theorem accepted0740 : minorantGammaCheck GammaPanel0740.certificate 638=true := by decide +kernel
noncomputable def cell0740 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0740.certificate 638 accepted0740
theorem accepted0741 : minorantGammaCheck GammaPanel0741.certificate 639=true := by decide +kernel
noncomputable def cell0741 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0741.certificate 639 accepted0741
theorem accepted0742 : minorantGammaCheck GammaPanel0742.certificate 640=true := by decide +kernel
noncomputable def cell0742 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0742.certificate 640 accepted0742
theorem accepted0743 : minorantGammaCheck GammaPanel0743.certificate 641=true := by decide +kernel
noncomputable def cell0743 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0743.certificate 641 accepted0743
noncomputable def cells : List CertifiedMinorantCell := [cell0736, cell0737, cell0738, cell0739, cell0740, cell0741, cell0742, cell0743]
theorem chainAccepted : minorantChainCheck (109/500) (113/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (109/500) (113/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0092
