module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0353

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0353
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2824 : minorantGammaCheck GammaPanel2824.certificate 1621=true := by decide +kernel
noncomputable def cell2824 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2824.certificate 1621 accepted2824
theorem accepted2825 : minorantGammaCheck GammaPanel2825.certificate 1621=true := by decide +kernel
noncomputable def cell2825 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2825.certificate 1621 accepted2825
theorem accepted2826 : minorantGammaCheck GammaPanel2826.certificate 1621=true := by decide +kernel
noncomputable def cell2826 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2826.certificate 1621 accepted2826
theorem accepted2827 : minorantGammaCheck GammaPanel2827.certificate 1621=true := by decide +kernel
noncomputable def cell2827 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2827.certificate 1621 accepted2827
theorem accepted2828 : minorantGammaCheck GammaPanel2828.certificate 1621=true := by decide +kernel
noncomputable def cell2828 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2828.certificate 1621 accepted2828
theorem accepted2829 : minorantGammaCheck GammaPanel2829.certificate 1621=true := by decide +kernel
noncomputable def cell2829 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2829.certificate 1621 accepted2829
theorem accepted2830 : minorantGammaCheck GammaPanel2830.certificate 1621=true := by decide +kernel
noncomputable def cell2830 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2830.certificate 1621 accepted2830
theorem accepted2831 : minorantGammaCheck GammaPanel2831.certificate 1621=true := by decide +kernel
noncomputable def cell2831 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2831.certificate 1621 accepted2831
noncomputable def cells : List CertifiedMinorantCell := [cell2824, cell2825, cell2826, cell2827, cell2828, cell2829, cell2830, cell2831]
theorem chainAccepted : minorantChainCheck (24937/25000) (12469/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24937/25000) (12469/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0353
