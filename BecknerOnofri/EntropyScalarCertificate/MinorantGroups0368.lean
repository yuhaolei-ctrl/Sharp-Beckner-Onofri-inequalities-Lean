import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0368
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0368
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2944 : minorantGammaCheck GammaPanel2944.certificate 1621=true := by decide +kernel
noncomputable def cell2944 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2944.certificate 1621 accepted2944
theorem accepted2945 : minorantGammaCheck GammaPanel2945.certificate 1621=true := by decide +kernel
noncomputable def cell2945 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2945.certificate 1621 accepted2945
theorem accepted2946 : minorantGammaCheck GammaPanel2946.certificate 1621=true := by decide +kernel
noncomputable def cell2946 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2946.certificate 1621 accepted2946
theorem accepted2947 : minorantGammaCheck GammaPanel2947.certificate 1621=true := by decide +kernel
noncomputable def cell2947 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2947.certificate 1621 accepted2947
theorem accepted2948 : minorantGammaCheck GammaPanel2948.certificate 1621=true := by decide +kernel
noncomputable def cell2948 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2948.certificate 1621 accepted2948
theorem accepted2949 : minorantGammaCheck GammaPanel2949.certificate 1621=true := by decide +kernel
noncomputable def cell2949 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2949.certificate 1621 accepted2949
theorem accepted2950 : minorantGammaCheck GammaPanel2950.certificate 1621=true := by decide +kernel
noncomputable def cell2950 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2950.certificate 1621 accepted2950
theorem accepted2951 : minorantGammaCheck GammaPanel2951.certificate 1621=true := by decide +kernel
noncomputable def cell2951 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2951.certificate 1621 accepted2951
noncomputable def cells : List CertifiedMinorantCell := [cell2944, cell2945, cell2946, cell2947, cell2948, cell2949, cell2950, cell2951]
theorem chainAccepted : minorantChainCheck (3119/3125) (24953/25000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (3119/3125) (24953/25000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0368
