import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0356
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0356
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2848 : minorantGammaCheck GammaPanel2848.certificate 1621=true := by decide +kernel
noncomputable def cell2848 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2848.certificate 1621 accepted2848
theorem accepted2849 : minorantGammaCheck GammaPanel2849.certificate 1621=true := by decide +kernel
noncomputable def cell2849 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2849.certificate 1621 accepted2849
theorem accepted2850 : minorantGammaCheck GammaPanel2850.certificate 1621=true := by decide +kernel
noncomputable def cell2850 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2850.certificate 1621 accepted2850
theorem accepted2851 : minorantGammaCheck GammaPanel2851.certificate 1621=true := by decide +kernel
noncomputable def cell2851 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2851.certificate 1621 accepted2851
theorem accepted2852 : minorantGammaCheck GammaPanel2852.certificate 1621=true := by decide +kernel
noncomputable def cell2852 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2852.certificate 1621 accepted2852
theorem accepted2853 : minorantGammaCheck GammaPanel2853.certificate 1621=true := by decide +kernel
noncomputable def cell2853 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2853.certificate 1621 accepted2853
theorem accepted2854 : minorantGammaCheck GammaPanel2854.certificate 1621=true := by decide +kernel
noncomputable def cell2854 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2854.certificate 1621 accepted2854
theorem accepted2855 : minorantGammaCheck GammaPanel2855.certificate 1621=true := by decide +kernel
noncomputable def cell2855 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2855.certificate 1621 accepted2855
noncomputable def cells : List CertifiedMinorantCell := [cell2848, cell2849, cell2850, cell2851, cell2852, cell2853, cell2854, cell2855]
theorem chainAccepted : minorantChainCheck (1247/1250) (24941/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1247/1250) (24941/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0356
