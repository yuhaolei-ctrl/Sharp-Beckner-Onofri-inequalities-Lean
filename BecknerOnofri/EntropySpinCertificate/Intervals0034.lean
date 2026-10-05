import BecknerOnofri.SpinCellAssembly
import BecknerOnofri.EntropyScalarCertificate.Minorant
import BecknerOnofri.EntropySpinCertificate.Candidates0034
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0034
open CandidateBatch0034 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0544 : AffinePiece := pieces[504]'(by decide +kernel)
theorem intervalAccepted0544 : candidateIntervalCheck candidate0544 (1653/10000) (331/2000) piece0544=true := by decide +kernel
noncomputable def cell0544 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0544 accepted0544 (1653/10000) (331/2000) piece0544
    intervalAccepted0544 (fun t => piece_le_psi ⟨504,by decide +kernel⟩ t)
def piece0545 : AffinePiece := pieces[505]'(by decide +kernel)
theorem intervalAccepted0545 : candidateIntervalCheck candidate0545 (331/2000) (1657/10000) piece0545=true := by decide +kernel
noncomputable def cell0545 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0545 accepted0545 (331/2000) (1657/10000) piece0545
    intervalAccepted0545 (fun t => piece_le_psi ⟨505,by decide +kernel⟩ t)
def piece0546 : AffinePiece := pieces[506]'(by decide +kernel)
theorem intervalAccepted0546 : candidateIntervalCheck candidate0546 (1657/10000) (1659/10000) piece0546=true := by decide +kernel
noncomputable def cell0546 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0546 accepted0546 (1657/10000) (1659/10000) piece0546
    intervalAccepted0546 (fun t => piece_le_psi ⟨506,by decide +kernel⟩ t)
def piece0547 : AffinePiece := pieces[507]'(by decide +kernel)
theorem intervalAccepted0547 : candidateIntervalCheck candidate0547 (1659/10000) (1661/10000) piece0547=true := by decide +kernel
noncomputable def cell0547 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0547 accepted0547 (1659/10000) (1661/10000) piece0547
    intervalAccepted0547 (fun t => piece_le_psi ⟨507,by decide +kernel⟩ t)
def piece0548 : AffinePiece := pieces[508]'(by decide +kernel)
theorem intervalAccepted0548 : candidateIntervalCheck candidate0548 (1661/10000) (1663/10000) piece0548=true := by decide +kernel
noncomputable def cell0548 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0548 accepted0548 (1661/10000) (1663/10000) piece0548
    intervalAccepted0548 (fun t => piece_le_psi ⟨508,by decide +kernel⟩ t)
def piece0549 : AffinePiece := pieces[509]'(by decide +kernel)
theorem intervalAccepted0549 : candidateIntervalCheck candidate0549 (1663/10000) (333/2000) piece0549=true := by decide +kernel
noncomputable def cell0549 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0549 accepted0549 (1663/10000) (333/2000) piece0549
    intervalAccepted0549 (fun t => piece_le_psi ⟨509,by decide +kernel⟩ t)
def piece0550 : AffinePiece := pieces[510]'(by decide +kernel)
theorem intervalAccepted0550 : candidateIntervalCheck candidate0550 (333/2000) (1667/10000) piece0550=true := by decide +kernel
noncomputable def cell0550 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0550 accepted0550 (333/2000) (1667/10000) piece0550
    intervalAccepted0550 (fun t => piece_le_psi ⟨510,by decide +kernel⟩ t)
def piece0551 : AffinePiece := pieces[511]'(by decide +kernel)
theorem intervalAccepted0551 : candidateIntervalCheck candidate0551 (1667/10000) (1669/10000) piece0551=true := by decide +kernel
noncomputable def cell0551 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0551 accepted0551 (1667/10000) (1669/10000) piece0551
    intervalAccepted0551 (fun t => piece_le_psi ⟨511,by decide +kernel⟩ t)
def piece0552 : AffinePiece := pieces[512]'(by decide +kernel)
theorem intervalAccepted0552 : candidateIntervalCheck candidate0552 (1669/10000) (1671/10000) piece0552=true := by decide +kernel
noncomputable def cell0552 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0552 accepted0552 (1669/10000) (1671/10000) piece0552
    intervalAccepted0552 (fun t => piece_le_psi ⟨512,by decide +kernel⟩ t)
def piece0553 : AffinePiece := pieces[513]'(by decide +kernel)
theorem intervalAccepted0553 : candidateIntervalCheck candidate0553 (1671/10000) (1673/10000) piece0553=true := by decide +kernel
noncomputable def cell0553 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0553 accepted0553 (1671/10000) (1673/10000) piece0553
    intervalAccepted0553 (fun t => piece_le_psi ⟨513,by decide +kernel⟩ t)
def piece0554 : AffinePiece := pieces[514]'(by decide +kernel)
theorem intervalAccepted0554 : candidateIntervalCheck candidate0554 (1673/10000) (67/400) piece0554=true := by decide +kernel
noncomputable def cell0554 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0554 accepted0554 (1673/10000) (67/400) piece0554
    intervalAccepted0554 (fun t => piece_le_psi ⟨514,by decide +kernel⟩ t)
def piece0555 : AffinePiece := pieces[515]'(by decide +kernel)
theorem intervalAccepted0555 : candidateIntervalCheck candidate0555 (67/400) (1677/10000) piece0555=true := by decide +kernel
noncomputable def cell0555 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0555 accepted0555 (67/400) (1677/10000) piece0555
    intervalAccepted0555 (fun t => piece_le_psi ⟨515,by decide +kernel⟩ t)
def piece0556 : AffinePiece := pieces[516]'(by decide +kernel)
theorem intervalAccepted0556 : candidateIntervalCheck candidate0556 (1677/10000) (1679/10000) piece0556=true := by decide +kernel
noncomputable def cell0556 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0556 accepted0556 (1677/10000) (1679/10000) piece0556
    intervalAccepted0556 (fun t => piece_le_psi ⟨516,by decide +kernel⟩ t)
def piece0557 : AffinePiece := pieces[517]'(by decide +kernel)
theorem intervalAccepted0557 : candidateIntervalCheck candidate0557 (1679/10000) (1681/10000) piece0557=true := by decide +kernel
noncomputable def cell0557 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0557 accepted0557 (1679/10000) (1681/10000) piece0557
    intervalAccepted0557 (fun t => piece_le_psi ⟨517,by decide +kernel⟩ t)
def piece0558 : AffinePiece := pieces[518]'(by decide +kernel)
theorem intervalAccepted0558 : candidateIntervalCheck candidate0558 (1681/10000) (1683/10000) piece0558=true := by decide +kernel
noncomputable def cell0558 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0558 accepted0558 (1681/10000) (1683/10000) piece0558
    intervalAccepted0558 (fun t => piece_le_psi ⟨518,by decide +kernel⟩ t)
def piece0559 : AffinePiece := pieces[519]'(by decide +kernel)
theorem intervalAccepted0559 : candidateIntervalCheck candidate0559 (1683/10000) (337/2000) piece0559=true := by decide +kernel
noncomputable def cell0559 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0559 accepted0559 (1683/10000) (337/2000) piece0559
    intervalAccepted0559 (fun t => piece_le_psi ⟨519,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0544, cell0545, cell0546, cell0547, cell0548, cell0549, cell0550, cell0551, cell0552, cell0553, cell0554, cell0555, cell0556, cell0557, cell0558, cell0559]
theorem chainAccepted : spinCellChainCheck (1653/10000) (337/2000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (1653/10000) (337/2000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0034
