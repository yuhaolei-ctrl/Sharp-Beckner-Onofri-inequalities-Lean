module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0369

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0369
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2952 : minorantGammaCheck GammaPanel2952.certificate 1621=true := by decide +kernel
noncomputable def cell2952 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2952.certificate 1621 accepted2952
theorem accepted2953 : minorantGammaCheck GammaPanel2953.certificate 1621=true := by decide +kernel
noncomputable def cell2953 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2953.certificate 1621 accepted2953
theorem accepted2954 : minorantGammaCheck GammaPanel2954.certificate 1621=true := by decide +kernel
noncomputable def cell2954 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2954.certificate 1621 accepted2954
theorem accepted2955 : minorantGammaCheck GammaPanel2955.certificate 1621=true := by decide +kernel
noncomputable def cell2955 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2955.certificate 1621 accepted2955
theorem accepted2956 : minorantGammaCheck GammaPanel2956.certificate 1621=true := by decide +kernel
noncomputable def cell2956 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2956.certificate 1621 accepted2956
theorem accepted2957 : minorantGammaCheck GammaPanel2957.certificate 1621=true := by decide +kernel
noncomputable def cell2957 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2957.certificate 1621 accepted2957
theorem accepted2958 : minorantGammaCheck GammaPanel2958.certificate 1621=true := by decide +kernel
noncomputable def cell2958 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2958.certificate 1621 accepted2958
theorem accepted2959 : minorantGammaCheck GammaPanel2959.certificate 1621=true := by decide +kernel
noncomputable def cell2959 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2959.certificate 1621 accepted2959
noncomputable def cells : List CertifiedMinorantCell := [cell2952, cell2953, cell2954, cell2955, cell2956, cell2957, cell2958, cell2959]
theorem chainAccepted : minorantChainCheck (24953/25000) (12477/12500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (24953/25000) (12477/12500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0369
