module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0008

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0008
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0064 : minorantGammaCheck GammaPanel0064.certificate 24=true := by decide +kernel
noncomputable def cell0064 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0064.certificate 24 accepted0064
theorem accepted0065 : minorantGammaCheck GammaPanel0065.certificate 25=true := by decide +kernel
noncomputable def cell0065 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0065.certificate 25 accepted0065
theorem accepted0066 : minorantGammaCheck GammaPanel0066.certificate 26=true := by decide +kernel
noncomputable def cell0066 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0066.certificate 26 accepted0066
theorem accepted0067 : minorantGammaCheck GammaPanel0067.certificate 27=true := by decide +kernel
noncomputable def cell0067 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0067.certificate 27 accepted0067
theorem accepted0068 : minorantGammaCheck GammaPanel0068.certificate 28=true := by decide +kernel
noncomputable def cell0068 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0068.certificate 28 accepted0068
theorem accepted0069 : minorantGammaCheck GammaPanel0069.certificate 29=true := by decide +kernel
noncomputable def cell0069 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0069.certificate 29 accepted0069
theorem accepted0070 : minorantGammaCheck GammaPanel0070.certificate 30=true := by decide +kernel
noncomputable def cell0070 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0070.certificate 30 accepted0070
theorem accepted0071 : minorantGammaCheck GammaPanel0071.certificate 31=true := by decide +kernel
noncomputable def cell0071 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0071.certificate 31 accepted0071
noncomputable def cells : List CertifiedMinorantCell := [cell0064, cell0065, cell0066, cell0067, cell0068, cell0069, cell0070, cell0071]
theorem chainAccepted : minorantChainCheck (693/10000) (709/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (693/10000) (709/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0008
