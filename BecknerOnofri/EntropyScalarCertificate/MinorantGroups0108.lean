import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0108
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0108
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0864 : minorantGammaCheck GammaPanel0864.certificate 762=true := by decide +kernel
noncomputable def cell0864 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0864.certificate 762 accepted0864
theorem accepted0865 : minorantGammaCheck GammaPanel0865.certificate 763=true := by decide +kernel
noncomputable def cell0865 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0865.certificate 763 accepted0865
theorem accepted0866 : minorantGammaCheck GammaPanel0866.certificate 764=true := by decide +kernel
noncomputable def cell0866 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0866.certificate 764 accepted0866
theorem accepted0867 : minorantGammaCheck GammaPanel0867.certificate 765=true := by decide +kernel
noncomputable def cell0867 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0867.certificate 765 accepted0867
theorem accepted0868 : minorantGammaCheck GammaPanel0868.certificate 766=true := by decide +kernel
noncomputable def cell0868 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0868.certificate 766 accepted0868
theorem accepted0869 : minorantGammaCheck GammaPanel0869.certificate 767=true := by decide +kernel
noncomputable def cell0869 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0869.certificate 767 accepted0869
theorem accepted0870 : minorantGammaCheck GammaPanel0870.certificate 768=true := by decide +kernel
noncomputable def cell0870 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0870.certificate 768 accepted0870
theorem accepted0871 : minorantGammaCheck GammaPanel0871.certificate 769=true := by decide +kernel
noncomputable def cell0871 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0871.certificate 769 accepted0871
noncomputable def cells : List CertifiedMinorantCell := [cell0864, cell0865, cell0866, cell0867, cell0868, cell0869, cell0870, cell0871]
theorem chainAccepted : minorantChainCheck (173/500) (177/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (173/500) (177/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0108
