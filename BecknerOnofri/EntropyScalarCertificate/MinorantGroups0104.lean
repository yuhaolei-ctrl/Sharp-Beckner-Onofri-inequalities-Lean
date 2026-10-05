import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0104
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0104
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0832 : minorantGammaCheck GammaPanel0832.certificate 730=true := by decide +kernel
noncomputable def cell0832 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0832.certificate 730 accepted0832
theorem accepted0833 : minorantGammaCheck GammaPanel0833.certificate 731=true := by decide +kernel
noncomputable def cell0833 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0833.certificate 731 accepted0833
theorem accepted0834 : minorantGammaCheck GammaPanel0834.certificate 732=true := by decide +kernel
noncomputable def cell0834 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0834.certificate 732 accepted0834
theorem accepted0835 : minorantGammaCheck GammaPanel0835.certificate 733=true := by decide +kernel
noncomputable def cell0835 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0835.certificate 733 accepted0835
theorem accepted0836 : minorantGammaCheck GammaPanel0836.certificate 734=true := by decide +kernel
noncomputable def cell0836 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0836.certificate 734 accepted0836
theorem accepted0837 : minorantGammaCheck GammaPanel0837.certificate 735=true := by decide +kernel
noncomputable def cell0837 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0837.certificate 735 accepted0837
theorem accepted0838 : minorantGammaCheck GammaPanel0838.certificate 736=true := by decide +kernel
noncomputable def cell0838 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0838.certificate 736 accepted0838
theorem accepted0839 : minorantGammaCheck GammaPanel0839.certificate 737=true := by decide +kernel
noncomputable def cell0839 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0839.certificate 737 accepted0839
noncomputable def cells : List CertifiedMinorantCell := [cell0832, cell0833, cell0834, cell0835, cell0836, cell0837, cell0838, cell0839]
theorem chainAccepted : minorantChainCheck (157/500) (161/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (157/500) (161/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0104
