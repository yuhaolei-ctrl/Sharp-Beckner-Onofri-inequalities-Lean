module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0354

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0354
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2832 : minorantGammaCheck GammaPanel2832.certificate 1621=true := by decide +kernel
noncomputable def cell2832 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2832.certificate 1621 accepted2832
theorem accepted2833 : minorantGammaCheck GammaPanel2833.certificate 1621=true := by decide +kernel
noncomputable def cell2833 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2833.certificate 1621 accepted2833
theorem accepted2834 : minorantGammaCheck GammaPanel2834.certificate 1621=true := by decide +kernel
noncomputable def cell2834 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2834.certificate 1621 accepted2834
theorem accepted2835 : minorantGammaCheck GammaPanel2835.certificate 1621=true := by decide +kernel
noncomputable def cell2835 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2835.certificate 1621 accepted2835
theorem accepted2836 : minorantGammaCheck GammaPanel2836.certificate 1621=true := by decide +kernel
noncomputable def cell2836 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2836.certificate 1621 accepted2836
theorem accepted2837 : minorantGammaCheck GammaPanel2837.certificate 1621=true := by decide +kernel
noncomputable def cell2837 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2837.certificate 1621 accepted2837
theorem accepted2838 : minorantGammaCheck GammaPanel2838.certificate 1621=true := by decide +kernel
noncomputable def cell2838 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2838.certificate 1621 accepted2838
theorem accepted2839 : minorantGammaCheck GammaPanel2839.certificate 1621=true := by decide +kernel
noncomputable def cell2839 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2839.certificate 1621 accepted2839
noncomputable def cells : List CertifiedMinorantCell := [cell2832, cell2833, cell2834, cell2835, cell2836, cell2837, cell2838, cell2839]
theorem chainAccepted : minorantChainCheck (12469/12500) (24939/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12469/12500) (24939/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0354
