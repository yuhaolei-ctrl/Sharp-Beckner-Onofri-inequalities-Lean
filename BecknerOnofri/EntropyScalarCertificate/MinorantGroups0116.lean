module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0116

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0116
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0928 : minorantGammaCheck GammaPanel0928.certificate 826=true := by decide +kernel
noncomputable def cell0928 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0928.certificate 826 accepted0928
theorem accepted0929 : minorantGammaCheck GammaPanel0929.certificate 827=true := by decide +kernel
noncomputable def cell0929 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0929.certificate 827 accepted0929
theorem accepted0930 : minorantGammaCheck GammaPanel0930.certificate 828=true := by decide +kernel
noncomputable def cell0930 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0930.certificate 828 accepted0930
theorem accepted0931 : minorantGammaCheck GammaPanel0931.certificate 829=true := by decide +kernel
noncomputable def cell0931 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0931.certificate 829 accepted0931
theorem accepted0932 : minorantGammaCheck GammaPanel0932.certificate 830=true := by decide +kernel
noncomputable def cell0932 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0932.certificate 830 accepted0932
theorem accepted0933 : minorantGammaCheck GammaPanel0933.certificate 831=true := by decide +kernel
noncomputable def cell0933 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0933.certificate 831 accepted0933
theorem accepted0934 : minorantGammaCheck GammaPanel0934.certificate 832=true := by decide +kernel
noncomputable def cell0934 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0934.certificate 832 accepted0934
theorem accepted0935 : minorantGammaCheck GammaPanel0935.certificate 833=true := by decide +kernel
noncomputable def cell0935 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0935.certificate 833 accepted0935
noncomputable def cells : List CertifiedMinorantCell := [cell0928, cell0929, cell0930, cell0931, cell0932, cell0933, cell0934, cell0935]
theorem chainAccepted : minorantChainCheck (41/100) (209/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (41/100) (209/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0116
