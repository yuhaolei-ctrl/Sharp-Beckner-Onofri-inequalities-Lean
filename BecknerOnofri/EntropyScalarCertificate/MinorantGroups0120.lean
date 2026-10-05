module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0120

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0120
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0960 : minorantGammaCheck GammaPanel0960.certificate 858=true := by decide +kernel
noncomputable def cell0960 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0960.certificate 858 accepted0960
theorem accepted0961 : minorantGammaCheck GammaPanel0961.certificate 859=true := by decide +kernel
noncomputable def cell0961 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0961.certificate 859 accepted0961
theorem accepted0962 : minorantGammaCheck GammaPanel0962.certificate 860=true := by decide +kernel
noncomputable def cell0962 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0962.certificate 860 accepted0962
theorem accepted0963 : minorantGammaCheck GammaPanel0963.certificate 861=true := by decide +kernel
noncomputable def cell0963 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0963.certificate 861 accepted0963
theorem accepted0964 : minorantGammaCheck GammaPanel0964.certificate 862=true := by decide +kernel
noncomputable def cell0964 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0964.certificate 862 accepted0964
theorem accepted0965 : minorantGammaCheck GammaPanel0965.certificate 863=true := by decide +kernel
noncomputable def cell0965 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0965.certificate 863 accepted0965
theorem accepted0966 : minorantGammaCheck GammaPanel0966.certificate 864=true := by decide +kernel
noncomputable def cell0966 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0966.certificate 864 accepted0966
theorem accepted0967 : minorantGammaCheck GammaPanel0967.certificate 865=true := by decide +kernel
noncomputable def cell0967 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0967.certificate 865 accepted0967
noncomputable def cells : List CertifiedMinorantCell := [cell0960, cell0961, cell0962, cell0963, cell0964, cell0965, cell0966, cell0967]
theorem chainAccepted : minorantChainCheck (221/500) (9/20) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (221/500) (9/20) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0120
