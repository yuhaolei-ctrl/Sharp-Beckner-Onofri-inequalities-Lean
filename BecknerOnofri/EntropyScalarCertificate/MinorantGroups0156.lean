module

public import BecknerOnofri.ScalarMinorantCell
public import BecknerOnofri.EntropyScalarCertificate.GammaGroups0156

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0156
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem accepted1248 : minorantGammaCheck GammaPanel1248.certificate 1146=true := by decide +kernel
noncomputable def cell1248 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1248.certificate 1146 accepted1248
theorem accepted1249 : minorantGammaCheck GammaPanel1249.certificate 1147=true := by decide +kernel
noncomputable def cell1249 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1249.certificate 1147 accepted1249
theorem accepted1250 : minorantGammaCheck GammaPanel1250.certificate 1148=true := by decide +kernel
noncomputable def cell1250 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1250.certificate 1148 accepted1250
theorem accepted1251 : minorantGammaCheck GammaPanel1251.certificate 1149=true := by decide +kernel
noncomputable def cell1251 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1251.certificate 1149 accepted1251
theorem accepted1252 : minorantGammaCheck GammaPanel1252.certificate 1150=true := by decide +kernel
noncomputable def cell1252 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1252.certificate 1150 accepted1252
theorem accepted1253 : minorantGammaCheck GammaPanel1253.certificate 1151=true := by decide +kernel
noncomputable def cell1253 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1253.certificate 1151 accepted1253
theorem accepted1254 : minorantGammaCheck GammaPanel1254.certificate 1152=true := by decide +kernel
noncomputable def cell1254 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1254.certificate 1152 accepted1254
theorem accepted1255 : minorantGammaCheck GammaPanel1255.certificate 1153=true := by decide +kernel
noncomputable def cell1255 : CertifiedMinorantCell := minorantCellOfGamma GammaPanel1255.certificate 1153 accepted1255
noncomputable def cells : List CertifiedMinorantCell := [cell1248, cell1249, cell1250, cell1251, cell1252, cell1253, cell1254, cell1255]
theorem chainAccepted : minorantChainCheck (73/100) (369/500) cells=true := by decide +kernel
noncomputable def block : CertifiedMinorantCell := minorantCellOfChain (73/100) (369/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.ScalarCertificate.MinorantBatch0156
