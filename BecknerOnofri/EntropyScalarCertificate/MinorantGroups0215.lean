module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0215

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0215
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1720 : minorantGammaCheck GammaPanel1720.certificate 1472=true := by decide +kernel
noncomputable def cell1720 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1720.certificate 1472 accepted1720
theorem accepted1721 : minorantGammaCheck GammaPanel1721.certificate 1472=true := by decide +kernel
noncomputable def cell1721 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1721.certificate 1472 accepted1721
theorem accepted1722 : minorantGammaCheck GammaPanel1722.certificate 1472=true := by decide +kernel
noncomputable def cell1722 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1722.certificate 1472 accepted1722
theorem accepted1723 : minorantGammaCheck GammaPanel1723.certificate 1472=true := by decide +kernel
noncomputable def cell1723 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1723.certificate 1472 accepted1723
theorem accepted1724 : minorantGammaCheck GammaPanel1724.certificate 1472=true := by decide +kernel
noncomputable def cell1724 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1724.certificate 1472 accepted1724
theorem accepted1725 : minorantGammaCheck GammaPanel1725.certificate 1472=true := by decide +kernel
noncomputable def cell1725 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1725.certificate 1472 accepted1725
theorem accepted1726 : minorantGammaCheck GammaPanel1726.certificate 1472=true := by decide +kernel
noncomputable def cell1726 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1726.certificate 1472 accepted1726
theorem accepted1727 : minorantGammaCheck GammaPanel1727.certificate 1472=true := by decide +kernel
noncomputable def cell1727 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1727.certificate 1472 accepted1727
noncomputable def cells : List CertifiedMinorantCell := [cell1720, cell1721, cell1722, cell1723, cell1724, cell1725, cell1726, cell1727]
theorem chainAccepted : minorantChainCheck (4321/5000) (173/200) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (4321/5000) (173/200) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0215
