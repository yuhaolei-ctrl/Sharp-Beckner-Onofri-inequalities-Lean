module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0119

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0119
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0952 : minorantGammaCheck GammaPanel0952.certificate 850=true := by decide +kernel
noncomputable def cell0952 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0952.certificate 850 accepted0952
theorem accepted0953 : minorantGammaCheck GammaPanel0953.certificate 851=true := by decide +kernel
noncomputable def cell0953 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0953.certificate 851 accepted0953
theorem accepted0954 : minorantGammaCheck GammaPanel0954.certificate 852=true := by decide +kernel
noncomputable def cell0954 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0954.certificate 852 accepted0954
theorem accepted0955 : minorantGammaCheck GammaPanel0955.certificate 853=true := by decide +kernel
noncomputable def cell0955 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0955.certificate 853 accepted0955
theorem accepted0956 : minorantGammaCheck GammaPanel0956.certificate 854=true := by decide +kernel
noncomputable def cell0956 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0956.certificate 854 accepted0956
theorem accepted0957 : minorantGammaCheck GammaPanel0957.certificate 855=true := by decide +kernel
noncomputable def cell0957 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0957.certificate 855 accepted0957
theorem accepted0958 : minorantGammaCheck GammaPanel0958.certificate 856=true := by decide +kernel
noncomputable def cell0958 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0958.certificate 856 accepted0958
theorem accepted0959 : minorantGammaCheck GammaPanel0959.certificate 857=true := by decide +kernel
noncomputable def cell0959 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0959.certificate 857 accepted0959
noncomputable def cells : List CertifiedMinorantCell := [cell0952, cell0953, cell0954, cell0955, cell0956, cell0957, cell0958, cell0959]
theorem chainAccepted : minorantChainCheck (217/500) (221/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (217/500) (221/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0119
