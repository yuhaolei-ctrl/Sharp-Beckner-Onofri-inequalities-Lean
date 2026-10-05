module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0112

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0112
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0896 : minorantGammaCheck GammaPanel0896.certificate 794=true := by decide +kernel
noncomputable def cell0896 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0896.certificate 794 accepted0896
theorem accepted0897 : minorantGammaCheck GammaPanel0897.certificate 795=true := by decide +kernel
noncomputable def cell0897 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0897.certificate 795 accepted0897
theorem accepted0898 : minorantGammaCheck GammaPanel0898.certificate 796=true := by decide +kernel
noncomputable def cell0898 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0898.certificate 796 accepted0898
theorem accepted0899 : minorantGammaCheck GammaPanel0899.certificate 797=true := by decide +kernel
noncomputable def cell0899 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0899.certificate 797 accepted0899
theorem accepted0900 : minorantGammaCheck GammaPanel0900.certificate 798=true := by decide +kernel
noncomputable def cell0900 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0900.certificate 798 accepted0900
theorem accepted0901 : minorantGammaCheck GammaPanel0901.certificate 799=true := by decide +kernel
noncomputable def cell0901 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0901.certificate 799 accepted0901
theorem accepted0902 : minorantGammaCheck GammaPanel0902.certificate 800=true := by decide +kernel
noncomputable def cell0902 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0902.certificate 800 accepted0902
theorem accepted0903 : minorantGammaCheck GammaPanel0903.certificate 801=true := by decide +kernel
noncomputable def cell0903 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0903.certificate 801 accepted0903
noncomputable def cells : List CertifiedMinorantCell := [cell0896, cell0897, cell0898, cell0899, cell0900, cell0901, cell0902, cell0903]
theorem chainAccepted : minorantChainCheck (189/500) (193/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (189/500) (193/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0112
