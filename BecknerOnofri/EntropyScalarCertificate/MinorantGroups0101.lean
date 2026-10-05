module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0101

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0101
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted0808 : minorantGammaCheck GammaPanel0808.certificate 706=true := by decide +kernel
noncomputable def cell0808 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0808.certificate 706 accepted0808
theorem accepted0809 : minorantGammaCheck GammaPanel0809.certificate 707=true := by decide +kernel
noncomputable def cell0809 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0809.certificate 707 accepted0809
theorem accepted0810 : minorantGammaCheck GammaPanel0810.certificate 708=true := by decide +kernel
noncomputable def cell0810 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0810.certificate 708 accepted0810
theorem accepted0811 : minorantGammaCheck GammaPanel0811.certificate 709=true := by decide +kernel
noncomputable def cell0811 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0811.certificate 709 accepted0811
theorem accepted0812 : minorantGammaCheck GammaPanel0812.certificate 710=true := by decide +kernel
noncomputable def cell0812 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0812.certificate 710 accepted0812
theorem accepted0813 : minorantGammaCheck GammaPanel0813.certificate 711=true := by decide +kernel
noncomputable def cell0813 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0813.certificate 711 accepted0813
theorem accepted0814 : minorantGammaCheck GammaPanel0814.certificate 712=true := by decide +kernel
noncomputable def cell0814 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0814.certificate 712 accepted0814
theorem accepted0815 : minorantGammaCheck GammaPanel0815.certificate 713=true := by decide +kernel
noncomputable def cell0815 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel0815.certificate 713 accepted0815
noncomputable def cells : List CertifiedMinorantCell := [cell0808, cell0809, cell0810, cell0811, cell0812, cell0813, cell0814, cell0815]
theorem chainAccepted : minorantChainCheck (29/100) (149/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (29/100) (149/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0101
