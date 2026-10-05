module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0384

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0384
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3072 : minorantGammaCheck GammaPanel3072.certificate 1621=true := by decide +kernel
noncomputable def cell3072 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3072.certificate 1621 accepted3072
theorem accepted3073 : minorantGammaCheck GammaPanel3073.certificate 1621=true := by decide +kernel
noncomputable def cell3073 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3073.certificate 1621 accepted3073
theorem accepted3074 : minorantGammaCheck GammaPanel3074.certificate 1621=true := by decide +kernel
noncomputable def cell3074 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3074.certificate 1621 accepted3074
theorem accepted3075 : minorantGammaCheck GammaPanel3075.certificate 1621=true := by decide +kernel
noncomputable def cell3075 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3075.certificate 1621 accepted3075
theorem accepted3076 : minorantGammaCheck GammaPanel3076.certificate 1621=true := by decide +kernel
noncomputable def cell3076 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3076.certificate 1621 accepted3076
theorem accepted3077 : minorantGammaCheck GammaPanel3077.certificate 1621=true := by decide +kernel
noncomputable def cell3077 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3077.certificate 1621 accepted3077
theorem accepted3078 : minorantGammaCheck GammaPanel3078.certificate 1621=true := by decide +kernel
noncomputable def cell3078 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3078.certificate 1621 accepted3078
theorem accepted3079 : minorantGammaCheck GammaPanel3079.certificate 1621=true := by decide +kernel
noncomputable def cell3079 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3079.certificate 1621 accepted3079
noncomputable def cells : List CertifiedMinorantCell := [cell3072, cell3073, cell3074, cell3075, cell3076, cell3077, cell3078, cell3079]
theorem chainAccepted : minorantChainCheck (3121/3125) (24969/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (3121/3125) (24969/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0384
