module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0382

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0382
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted3056 : minorantGammaCheck GammaPanel3056.certificate 1621=true := by decide +kernel
noncomputable def cell3056 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3056.certificate 1621 accepted3056
theorem accepted3057 : minorantGammaCheck GammaPanel3057.certificate 1621=true := by decide +kernel
noncomputable def cell3057 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3057.certificate 1621 accepted3057
theorem accepted3058 : minorantGammaCheck GammaPanel3058.certificate 1621=true := by decide +kernel
noncomputable def cell3058 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3058.certificate 1621 accepted3058
theorem accepted3059 : minorantGammaCheck GammaPanel3059.certificate 1621=true := by decide +kernel
noncomputable def cell3059 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3059.certificate 1621 accepted3059
theorem accepted3060 : minorantGammaCheck GammaPanel3060.certificate 1621=true := by decide +kernel
noncomputable def cell3060 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3060.certificate 1621 accepted3060
theorem accepted3061 : minorantGammaCheck GammaPanel3061.certificate 1621=true := by decide +kernel
noncomputable def cell3061 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3061.certificate 1621 accepted3061
theorem accepted3062 : minorantGammaCheck GammaPanel3062.certificate 1621=true := by decide +kernel
noncomputable def cell3062 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3062.certificate 1621 accepted3062
theorem accepted3063 : minorantGammaCheck GammaPanel3063.certificate 1621=true := by decide +kernel
noncomputable def cell3063 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel3063.certificate 1621 accepted3063
noncomputable def cells : List CertifiedMinorantCell := [cell3056, cell3057, cell3058, cell3059, cell3060, cell3061, cell3062, cell3063]
theorem chainAccepted : minorantChainCheck (12483/12500) (24967/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (12483/12500) (24967/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0382
