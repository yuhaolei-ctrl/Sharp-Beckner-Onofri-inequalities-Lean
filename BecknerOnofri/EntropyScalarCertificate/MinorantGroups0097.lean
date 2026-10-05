module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0097

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0097
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0776 : minorantGammaCheck GammaPanel0776.certificate 674=true := by decide +kernel
noncomputable def cell0776 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0776.certificate 674 accepted0776
theorem accepted0777 : minorantGammaCheck GammaPanel0777.certificate 675=true := by decide +kernel
noncomputable def cell0777 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0777.certificate 675 accepted0777
theorem accepted0778 : minorantGammaCheck GammaPanel0778.certificate 676=true := by decide +kernel
noncomputable def cell0778 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0778.certificate 676 accepted0778
theorem accepted0779 : minorantGammaCheck GammaPanel0779.certificate 677=true := by decide +kernel
noncomputable def cell0779 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0779.certificate 677 accepted0779
theorem accepted0780 : minorantGammaCheck GammaPanel0780.certificate 678=true := by decide +kernel
noncomputable def cell0780 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0780.certificate 678 accepted0780
theorem accepted0781 : minorantGammaCheck GammaPanel0781.certificate 679=true := by decide +kernel
noncomputable def cell0781 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0781.certificate 679 accepted0781
theorem accepted0782 : minorantGammaCheck GammaPanel0782.certificate 680=true := by decide +kernel
noncomputable def cell0782 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0782.certificate 680 accepted0782
theorem accepted0783 : minorantGammaCheck GammaPanel0783.certificate 681=true := by decide +kernel
noncomputable def cell0783 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0783.certificate 681 accepted0783
noncomputable def cells : List CertifiedMinorantCell := [cell0776, cell0777, cell0778, cell0779, cell0780, cell0781, cell0782, cell0783]
theorem chainAccepted : minorantChainCheck (129/500) (133/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (129/500) (133/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0097
