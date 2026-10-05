import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0100
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0100
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0800 : minorantGammaCheck GammaPanel0800.certificate 698=true := by decide +kernel
noncomputable def cell0800 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0800.certificate 698 accepted0800
theorem accepted0801 : minorantGammaCheck GammaPanel0801.certificate 699=true := by decide +kernel
noncomputable def cell0801 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0801.certificate 699 accepted0801
theorem accepted0802 : minorantGammaCheck GammaPanel0802.certificate 700=true := by decide +kernel
noncomputable def cell0802 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0802.certificate 700 accepted0802
theorem accepted0803 : minorantGammaCheck GammaPanel0803.certificate 701=true := by decide +kernel
noncomputable def cell0803 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0803.certificate 701 accepted0803
theorem accepted0804 : minorantGammaCheck GammaPanel0804.certificate 702=true := by decide +kernel
noncomputable def cell0804 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0804.certificate 702 accepted0804
theorem accepted0805 : minorantGammaCheck GammaPanel0805.certificate 703=true := by decide +kernel
noncomputable def cell0805 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0805.certificate 703 accepted0805
theorem accepted0806 : minorantGammaCheck GammaPanel0806.certificate 704=true := by decide +kernel
noncomputable def cell0806 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0806.certificate 704 accepted0806
theorem accepted0807 : minorantGammaCheck GammaPanel0807.certificate 705=true := by decide +kernel
noncomputable def cell0807 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0807.certificate 705 accepted0807
noncomputable def cells : List CertifiedMinorantCell := [cell0800, cell0801, cell0802, cell0803, cell0804, cell0805, cell0806, cell0807]
theorem chainAccepted : minorantChainCheck (141/500) (29/100) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (141/500) (29/100) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0100
