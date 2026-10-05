module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0081

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0081
open CandidateBatch0081 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1296 : AffinePiece := pieces[1194]'(by decide +kernel)
theorem intervalAccepted1296 : candidateIntervalCheck candidate1296 (389/500) (779/1000) piece1296=true := by decide +kernel
noncomputable def cell1296 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1296 accepted1296 (389/500) (779/1000) piece1296
    intervalAccepted1296 (fun t => piece_le_psi ⟨1194,by decide +kernel⟩ t)
def piece1297 : AffinePiece := pieces[1195]'(by decide +kernel)
theorem intervalAccepted1297 : candidateIntervalCheck candidate1297 (779/1000) (39/50) piece1297=true := by decide +kernel
noncomputable def cell1297 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1297 accepted1297 (779/1000) (39/50) piece1297
    intervalAccepted1297 (fun t => piece_le_psi ⟨1195,by decide +kernel⟩ t)
def piece1298 : AffinePiece := pieces[1196]'(by decide +kernel)
theorem intervalAccepted1298 : candidateIntervalCheck candidate1298 (39/50) (781/1000) piece1298=true := by decide +kernel
noncomputable def cell1298 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1298 accepted1298 (39/50) (781/1000) piece1298
    intervalAccepted1298 (fun t => piece_le_psi ⟨1196,by decide +kernel⟩ t)
def piece1299 : AffinePiece := pieces[1197]'(by decide +kernel)
theorem intervalAccepted1299 : candidateIntervalCheck candidate1299 (781/1000) (391/500) piece1299=true := by decide +kernel
noncomputable def cell1299 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1299 accepted1299 (781/1000) (391/500) piece1299
    intervalAccepted1299 (fun t => piece_le_psi ⟨1197,by decide +kernel⟩ t)
def piece1300 : AffinePiece := pieces[1198]'(by decide +kernel)
theorem intervalAccepted1300 : candidateIntervalCheck candidate1300 (391/500) (783/1000) piece1300=true := by decide +kernel
noncomputable def cell1300 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1300 accepted1300 (391/500) (783/1000) piece1300
    intervalAccepted1300 (fun t => piece_le_psi ⟨1198,by decide +kernel⟩ t)
def piece1301 : AffinePiece := pieces[1199]'(by decide +kernel)
theorem intervalAccepted1301 : candidateIntervalCheck candidate1301 (783/1000) (98/125) piece1301=true := by decide +kernel
noncomputable def cell1301 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1301 accepted1301 (783/1000) (98/125) piece1301
    intervalAccepted1301 (fun t => piece_le_psi ⟨1199,by decide +kernel⟩ t)
def piece1302 : AffinePiece := pieces[1200]'(by decide +kernel)
theorem intervalAccepted1302 : candidateIntervalCheck candidate1302 (98/125) (157/200) piece1302=true := by decide +kernel
noncomputable def cell1302 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1302 accepted1302 (98/125) (157/200) piece1302
    intervalAccepted1302 (fun t => piece_le_psi ⟨1200,by decide +kernel⟩ t)
def piece1303 : AffinePiece := pieces[1201]'(by decide +kernel)
theorem intervalAccepted1303 : candidateIntervalCheck candidate1303 (157/200) (393/500) piece1303=true := by decide +kernel
noncomputable def cell1303 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1303 accepted1303 (157/200) (393/500) piece1303
    intervalAccepted1303 (fun t => piece_le_psi ⟨1201,by decide +kernel⟩ t)
def piece1304 : AffinePiece := pieces[1202]'(by decide +kernel)
theorem intervalAccepted1304 : candidateIntervalCheck candidate1304 (393/500) (787/1000) piece1304=true := by decide +kernel
noncomputable def cell1304 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1304 accepted1304 (393/500) (787/1000) piece1304
    intervalAccepted1304 (fun t => piece_le_psi ⟨1202,by decide +kernel⟩ t)
def piece1305 : AffinePiece := pieces[1203]'(by decide +kernel)
theorem intervalAccepted1305 : candidateIntervalCheck candidate1305 (787/1000) (197/250) piece1305=true := by decide +kernel
noncomputable def cell1305 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1305 accepted1305 (787/1000) (197/250) piece1305
    intervalAccepted1305 (fun t => piece_le_psi ⟨1203,by decide +kernel⟩ t)
def piece1306 : AffinePiece := pieces[1204]'(by decide +kernel)
theorem intervalAccepted1306 : candidateIntervalCheck candidate1306 (197/250) (789/1000) piece1306=true := by decide +kernel
noncomputable def cell1306 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1306 accepted1306 (197/250) (789/1000) piece1306
    intervalAccepted1306 (fun t => piece_le_psi ⟨1204,by decide +kernel⟩ t)
def piece1307 : AffinePiece := pieces[1205]'(by decide +kernel)
theorem intervalAccepted1307 : candidateIntervalCheck candidate1307 (789/1000) (79/100) piece1307=true := by decide +kernel
noncomputable def cell1307 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1307 accepted1307 (789/1000) (79/100) piece1307
    intervalAccepted1307 (fun t => piece_le_psi ⟨1205,by decide +kernel⟩ t)
def piece1308 : AffinePiece := pieces[1206]'(by decide +kernel)
theorem intervalAccepted1308 : candidateIntervalCheck candidate1308 (79/100) (791/1000) piece1308=true := by decide +kernel
noncomputable def cell1308 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1308 accepted1308 (79/100) (791/1000) piece1308
    intervalAccepted1308 (fun t => piece_le_psi ⟨1206,by decide +kernel⟩ t)
def piece1309 : AffinePiece := pieces[1207]'(by decide +kernel)
theorem intervalAccepted1309 : candidateIntervalCheck candidate1309 (791/1000) (99/125) piece1309=true := by decide +kernel
noncomputable def cell1309 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1309 accepted1309 (791/1000) (99/125) piece1309
    intervalAccepted1309 (fun t => piece_le_psi ⟨1207,by decide +kernel⟩ t)
def piece1310 : AffinePiece := pieces[1208]'(by decide +kernel)
theorem intervalAccepted1310 : candidateIntervalCheck candidate1310 (99/125) (793/1000) piece1310=true := by decide +kernel
noncomputable def cell1310 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1310 accepted1310 (99/125) (793/1000) piece1310
    intervalAccepted1310 (fun t => piece_le_psi ⟨1208,by decide +kernel⟩ t)
def piece1311 : AffinePiece := pieces[1209]'(by decide +kernel)
theorem intervalAccepted1311 : candidateIntervalCheck candidate1311 (793/1000) (397/500) piece1311=true := by decide +kernel
noncomputable def cell1311 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1311 accepted1311 (793/1000) (397/500) piece1311
    intervalAccepted1311 (fun t => piece_le_psi ⟨1209,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1296, cell1297, cell1298, cell1299, cell1300, cell1301, cell1302, cell1303, cell1304, cell1305, cell1306, cell1307, cell1308, cell1309, cell1310, cell1311]
theorem chainAccepted : spinCellChainCheck (389/500) (397/500) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (389/500) (397/500) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0081
