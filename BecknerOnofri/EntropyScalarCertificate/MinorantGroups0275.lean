import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0275
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0275
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2200 : minorantGammaCheck GammaPanel2200.certificate 1621=true := by decide +kernel
noncomputable def cell2200 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2200.certificate 1621 accepted2200
theorem accepted2201 : minorantGammaCheck GammaPanel2201.certificate 1621=true := by decide +kernel
noncomputable def cell2201 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2201.certificate 1621 accepted2201
theorem accepted2202 : minorantGammaCheck GammaPanel2202.certificate 1621=true := by decide +kernel
noncomputable def cell2202 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2202.certificate 1621 accepted2202
theorem accepted2203 : minorantGammaCheck GammaPanel2203.certificate 1621=true := by decide +kernel
noncomputable def cell2203 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2203.certificate 1621 accepted2203
theorem accepted2204 : minorantGammaCheck GammaPanel2204.certificate 1621=true := by decide +kernel
noncomputable def cell2204 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2204.certificate 1621 accepted2204
theorem accepted2205 : minorantGammaCheck GammaPanel2205.certificate 1621=true := by decide +kernel
noncomputable def cell2205 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2205.certificate 1621 accepted2205
theorem accepted2206 : minorantGammaCheck GammaPanel2206.certificate 1621=true := by decide +kernel
noncomputable def cell2206 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2206.certificate 1621 accepted2206
theorem accepted2207 : minorantGammaCheck GammaPanel2207.certificate 1621=true := by decide +kernel
noncomputable def cell2207 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2207.certificate 1621 accepted2207
noncomputable def cells : List CertifiedMinorantCell := [cell2200, cell2201, cell2202, cell2203, cell2204, cell2205, cell2206, cell2207]
theorem chainAccepted : minorantChainCheck (4861/5000) (973/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4861/5000) (973/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0275
