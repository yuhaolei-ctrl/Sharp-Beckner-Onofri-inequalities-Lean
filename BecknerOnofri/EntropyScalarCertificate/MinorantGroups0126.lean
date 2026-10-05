module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0126

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0126
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1008 : minorantGammaCheck GammaPanel1008.certificate 906=true := by decide +kernel
noncomputable def cell1008 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1008.certificate 906 accepted1008
theorem accepted1009 : minorantGammaCheck GammaPanel1009.certificate 907=true := by decide +kernel
noncomputable def cell1009 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1009.certificate 907 accepted1009
theorem accepted1010 : minorantGammaCheck GammaPanel1010.certificate 908=true := by decide +kernel
noncomputable def cell1010 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1010.certificate 908 accepted1010
theorem accepted1011 : minorantGammaCheck GammaPanel1011.certificate 909=true := by decide +kernel
noncomputable def cell1011 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1011.certificate 909 accepted1011
theorem accepted1012 : minorantGammaCheck GammaPanel1012.certificate 910=true := by decide +kernel
noncomputable def cell1012 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1012.certificate 910 accepted1012
theorem accepted1013 : minorantGammaCheck GammaPanel1013.certificate 911=true := by decide +kernel
noncomputable def cell1013 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1013.certificate 911 accepted1013
theorem accepted1014 : minorantGammaCheck GammaPanel1014.certificate 912=true := by decide +kernel
noncomputable def cell1014 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1014.certificate 912 accepted1014
theorem accepted1015 : minorantGammaCheck GammaPanel1015.certificate 913=true := by decide +kernel
noncomputable def cell1015 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1015.certificate 913 accepted1015
noncomputable def cells : List CertifiedMinorantCell := [cell1008, cell1009, cell1010, cell1011, cell1012, cell1013, cell1014, cell1015]
theorem chainAccepted : minorantChainCheck (49/100) (249/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (49/100) (249/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0126
