module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0262

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0262
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2096 : minorantGammaCheck GammaPanel2096.certificate 1621=true := by decide +kernel
noncomputable def cell2096 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2096.certificate 1621 accepted2096
theorem accepted2097 : minorantGammaCheck GammaPanel2097.certificate 1621=true := by decide +kernel
noncomputable def cell2097 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2097.certificate 1621 accepted2097
theorem accepted2098 : minorantGammaCheck GammaPanel2098.certificate 1621=true := by decide +kernel
noncomputable def cell2098 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2098.certificate 1621 accepted2098
theorem accepted2099 : minorantGammaCheck GammaPanel2099.certificate 1621=true := by decide +kernel
noncomputable def cell2099 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2099.certificate 1621 accepted2099
theorem accepted2100 : minorantGammaCheck GammaPanel2100.certificate 1621=true := by decide +kernel
noncomputable def cell2100 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2100.certificate 1621 accepted2100
theorem accepted2101 : minorantGammaCheck GammaPanel2101.certificate 1621=true := by decide +kernel
noncomputable def cell2101 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2101.certificate 1621 accepted2101
theorem accepted2102 : minorantGammaCheck GammaPanel2102.certificate 1621=true := by decide +kernel
noncomputable def cell2102 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2102.certificate 1621 accepted2102
theorem accepted2103 : minorantGammaCheck GammaPanel2103.certificate 1621=true := by decide +kernel
noncomputable def cell2103 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2103.certificate 1621 accepted2103
noncomputable def cells : List CertifiedMinorantCell := [cell2096, cell2097, cell2098, cell2099, cell2100, cell2101, cell2102, cell2103]
theorem chainAccepted : minorantChainCheck (4809/5000) (4813/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4809/5000) (4813/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0262
