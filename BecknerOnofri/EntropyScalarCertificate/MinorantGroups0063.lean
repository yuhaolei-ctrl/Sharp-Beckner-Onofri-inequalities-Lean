module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0063

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0063
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0504 : minorantGammaCheck GammaPanel0504.certificate 464=true := by decide +kernel
noncomputable def cell0504 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0504.certificate 464 accepted0504
theorem accepted0505 : minorantGammaCheck GammaPanel0505.certificate 465=true := by decide +kernel
noncomputable def cell0505 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0505.certificate 465 accepted0505
theorem accepted0506 : minorantGammaCheck GammaPanel0506.certificate 466=true := by decide +kernel
noncomputable def cell0506 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0506.certificate 466 accepted0506
theorem accepted0507 : minorantGammaCheck GammaPanel0507.certificate 467=true := by decide +kernel
noncomputable def cell0507 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0507.certificate 467 accepted0507
theorem accepted0508 : minorantGammaCheck GammaPanel0508.certificate 468=true := by decide +kernel
noncomputable def cell0508 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0508.certificate 468 accepted0508
theorem accepted0509 : minorantGammaCheck GammaPanel0509.certificate 469=true := by decide +kernel
noncomputable def cell0509 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0509.certificate 469 accepted0509
theorem accepted0510 : minorantGammaCheck GammaPanel0510.certificate 470=true := by decide +kernel
noncomputable def cell0510 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0510.certificate 470 accepted0510
theorem accepted0511 : minorantGammaCheck GammaPanel0511.certificate 471=true := by decide +kernel
noncomputable def cell0511 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0511.certificate 471 accepted0511
noncomputable def cells : List CertifiedMinorantCell := [cell0504, cell0505, cell0506, cell0507, cell0508, cell0509, cell0510, cell0511]
theorem chainAccepted : minorantChainCheck (1573/10000) (1589/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (1573/10000) (1589/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0063
