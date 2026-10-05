module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0109

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0109
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0872 : minorantGammaCheck GammaPanel0872.certificate 770=true := by decide +kernel
noncomputable def cell0872 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0872.certificate 770 accepted0872
theorem accepted0873 : minorantGammaCheck GammaPanel0873.certificate 771=true := by decide +kernel
noncomputable def cell0873 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0873.certificate 771 accepted0873
theorem accepted0874 : minorantGammaCheck GammaPanel0874.certificate 772=true := by decide +kernel
noncomputable def cell0874 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0874.certificate 772 accepted0874
theorem accepted0875 : minorantGammaCheck GammaPanel0875.certificate 773=true := by decide +kernel
noncomputable def cell0875 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0875.certificate 773 accepted0875
theorem accepted0876 : minorantGammaCheck GammaPanel0876.certificate 774=true := by decide +kernel
noncomputable def cell0876 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0876.certificate 774 accepted0876
theorem accepted0877 : minorantGammaCheck GammaPanel0877.certificate 775=true := by decide +kernel
noncomputable def cell0877 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0877.certificate 775 accepted0877
theorem accepted0878 : minorantGammaCheck GammaPanel0878.certificate 776=true := by decide +kernel
noncomputable def cell0878 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0878.certificate 776 accepted0878
theorem accepted0879 : minorantGammaCheck GammaPanel0879.certificate 777=true := by decide +kernel
noncomputable def cell0879 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0879.certificate 777 accepted0879
noncomputable def cells : List CertifiedMinorantCell := [cell0872, cell0873, cell0874, cell0875, cell0876, cell0877, cell0878, cell0879]
theorem chainAccepted : minorantChainCheck (177/500) (181/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (177/500) (181/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0109
