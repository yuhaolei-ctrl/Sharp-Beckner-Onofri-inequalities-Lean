module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0191

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0191
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1528 : minorantGammaCheck GammaPanel1528.certificate 1286=true := by decide +kernel
noncomputable def cell1528 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1528.certificate 1286 accepted1528
theorem accepted1529 : minorantGammaCheck GammaPanel1529.certificate 1287=true := by decide +kernel
noncomputable def cell1529 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1529.certificate 1287 accepted1529
theorem accepted1530 : minorantGammaCheck GammaPanel1530.certificate 1288=true := by decide +kernel
noncomputable def cell1530 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1530.certificate 1288 accepted1530
theorem accepted1531 : minorantGammaCheck GammaPanel1531.certificate 1289=true := by decide +kernel
noncomputable def cell1531 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1531.certificate 1289 accepted1531
theorem accepted1532 : minorantGammaCheck GammaPanel1532.certificate 1290=true := by decide +kernel
noncomputable def cell1532 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1532.certificate 1290 accepted1532
theorem accepted1533 : minorantGammaCheck GammaPanel1533.certificate 1291=true := by decide +kernel
noncomputable def cell1533 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1533.certificate 1291 accepted1533
theorem accepted1534 : minorantGammaCheck GammaPanel1534.certificate 1292=true := by decide +kernel
noncomputable def cell1534 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1534.certificate 1292 accepted1534
theorem accepted1535 : minorantGammaCheck GammaPanel1535.certificate 1293=true := by decide +kernel
noncomputable def cell1535 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1535.certificate 1293 accepted1535
noncomputable def cells : List CertifiedMinorantCell := [cell1528, cell1529, cell1530, cell1531, cell1532, cell1533, cell1534, cell1535]
theorem chainAccepted : minorantChainCheck (169/200) (4229/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (169/200) (4229/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0191
