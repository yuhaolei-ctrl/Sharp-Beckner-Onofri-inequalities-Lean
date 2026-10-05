module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0350

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0350
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2800 : minorantGammaCheck GammaPanel2800.certificate 1621=true := by decide +kernel
noncomputable def cell2800 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2800.certificate 1621 accepted2800
theorem accepted2801 : minorantGammaCheck GammaPanel2801.certificate 1621=true := by decide +kernel
noncomputable def cell2801 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2801.certificate 1621 accepted2801
theorem accepted2802 : minorantGammaCheck GammaPanel2802.certificate 1621=true := by decide +kernel
noncomputable def cell2802 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2802.certificate 1621 accepted2802
theorem accepted2803 : minorantGammaCheck GammaPanel2803.certificate 1621=true := by decide +kernel
noncomputable def cell2803 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2803.certificate 1621 accepted2803
theorem accepted2804 : minorantGammaCheck GammaPanel2804.certificate 1621=true := by decide +kernel
noncomputable def cell2804 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2804.certificate 1621 accepted2804
theorem accepted2805 : minorantGammaCheck GammaPanel2805.certificate 1621=true := by decide +kernel
noncomputable def cell2805 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2805.certificate 1621 accepted2805
theorem accepted2806 : minorantGammaCheck GammaPanel2806.certificate 1621=true := by decide +kernel
noncomputable def cell2806 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2806.certificate 1621 accepted2806
theorem accepted2807 : minorantGammaCheck GammaPanel2807.certificate 1621=true := by decide +kernel
noncomputable def cell2807 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2807.certificate 1621 accepted2807
noncomputable def cells : List CertifiedMinorantCell := [cell2800, cell2801, cell2802, cell2803, cell2804, cell2805, cell2806, cell2807]
theorem chainAccepted : minorantChainCheck (12467/12500) (4987/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12467/12500) (4987/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0350
