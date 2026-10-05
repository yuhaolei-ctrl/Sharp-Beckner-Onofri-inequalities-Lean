module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0200

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0200
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1600 : minorantGammaCheck GammaPanel1600.certificate 1358=true := by decide +kernel
noncomputable def cell1600 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1600.certificate 1358 accepted1600
theorem accepted1601 : minorantGammaCheck GammaPanel1601.certificate 1359=true := by decide +kernel
noncomputable def cell1601 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1601.certificate 1359 accepted1601
theorem accepted1602 : minorantGammaCheck GammaPanel1602.certificate 1360=true := by decide +kernel
noncomputable def cell1602 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1602.certificate 1360 accepted1602
theorem accepted1603 : minorantGammaCheck GammaPanel1603.certificate 1361=true := by decide +kernel
noncomputable def cell1603 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1603.certificate 1361 accepted1603
theorem accepted1604 : minorantGammaCheck GammaPanel1604.certificate 1362=true := by decide +kernel
noncomputable def cell1604 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1604.certificate 1362 accepted1604
theorem accepted1605 : minorantGammaCheck GammaPanel1605.certificate 1363=true := by decide +kernel
noncomputable def cell1605 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1605.certificate 1363 accepted1605
theorem accepted1606 : minorantGammaCheck GammaPanel1606.certificate 1364=true := by decide +kernel
noncomputable def cell1606 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1606.certificate 1364 accepted1606
theorem accepted1607 : minorantGammaCheck GammaPanel1607.certificate 1365=true := by decide +kernel
noncomputable def cell1607 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1607.certificate 1365 accepted1607
noncomputable def cells : List CertifiedMinorantCell := [cell1600, cell1601, cell1602, cell1603, cell1604, cell1605, cell1606, cell1607]
theorem chainAccepted : minorantChainCheck (4261/5000) (853/1000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4261/5000) (853/1000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0200
