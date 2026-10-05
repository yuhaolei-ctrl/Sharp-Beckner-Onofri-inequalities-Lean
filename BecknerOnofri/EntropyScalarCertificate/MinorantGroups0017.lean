import BecknerOnofri.ScalarMinorantCell
import BecknerOnofri.EntropyScalarCertificate.GammaGroups0017
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0017
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0136 : minorantGammaCheck GammaPanel0136.certificate 96=true := by decide +kernel
noncomputable def cell0136 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0136.certificate 96 accepted0136
theorem accepted0137 : minorantGammaCheck GammaPanel0137.certificate 97=true := by decide +kernel
noncomputable def cell0137 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0137.certificate 97 accepted0137
theorem accepted0138 : minorantGammaCheck GammaPanel0138.certificate 98=true := by decide +kernel
noncomputable def cell0138 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0138.certificate 98 accepted0138
theorem accepted0139 : minorantGammaCheck GammaPanel0139.certificate 99=true := by decide +kernel
noncomputable def cell0139 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0139.certificate 99 accepted0139
theorem accepted0140 : minorantGammaCheck GammaPanel0140.certificate 100=true := by decide +kernel
noncomputable def cell0140 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0140.certificate 100 accepted0140
theorem accepted0141 : minorantGammaCheck GammaPanel0141.certificate 101=true := by decide +kernel
noncomputable def cell0141 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0141.certificate 101 accepted0141
theorem accepted0142 : minorantGammaCheck GammaPanel0142.certificate 102=true := by decide +kernel
noncomputable def cell0142 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0142.certificate 102 accepted0142
theorem accepted0143 : minorantGammaCheck GammaPanel0143.certificate 103=true := by decide +kernel
noncomputable def cell0143 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0143.certificate 103 accepted0143
noncomputable def cells : List CertifiedMinorantCell := [cell0136, cell0137, cell0138, cell0139, cell0140, cell0141, cell0142, cell0143]
theorem chainAccepted : minorantChainCheck (837/10000) (853/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (837/10000) (853/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0017
