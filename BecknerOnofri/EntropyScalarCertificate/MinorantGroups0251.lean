module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0251

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0251
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted2008 : minorantGammaCheck GammaPanel2008.certificate 1621=true := by decide +kernel
noncomputable def cell2008 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2008.certificate 1621 accepted2008
theorem accepted2009 : minorantGammaCheck GammaPanel2009.certificate 1621=true := by decide +kernel
noncomputable def cell2009 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2009.certificate 1621 accepted2009
theorem accepted2010 : minorantGammaCheck GammaPanel2010.certificate 1621=true := by decide +kernel
noncomputable def cell2010 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2010.certificate 1621 accepted2010
theorem accepted2011 : minorantGammaCheck GammaPanel2011.certificate 1621=true := by decide +kernel
noncomputable def cell2011 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2011.certificate 1621 accepted2011
theorem accepted2012 : minorantGammaCheck GammaPanel2012.certificate 1621=true := by decide +kernel
noncomputable def cell2012 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2012.certificate 1621 accepted2012
theorem accepted2013 : minorantGammaCheck GammaPanel2013.certificate 1621=true := by decide +kernel
noncomputable def cell2013 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2013.certificate 1621 accepted2013
theorem accepted2014 : minorantGammaCheck GammaPanel2014.certificate 1621=true := by decide +kernel
noncomputable def cell2014 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2014.certificate 1621 accepted2014
theorem accepted2015 : minorantGammaCheck GammaPanel2015.certificate 1621=true := by decide +kernel
noncomputable def cell2015 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel2015.certificate 1621 accepted2015
noncomputable def cells : List CertifiedMinorantCell := [cell2008, cell2009, cell2010, cell2011, cell2012, cell2013, cell2014, cell2015]
theorem chainAccepted : minorantChainCheck (953/1000) (4769/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (953/1000) (4769/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0251
