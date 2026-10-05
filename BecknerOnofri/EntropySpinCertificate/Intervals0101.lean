module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0101

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0101
open CandidateBatch0101 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece1616 : AffinePiece := pieces[1374]'(by decide +kernel)
theorem intervalAccepted1616 : candidateIntervalCheck candidate1616 (4269/5000) (8539/10000) piece1616=true := by decide +kernel
noncomputable def cell1616 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1616 accepted1616 (4269/5000) (8539/10000) piece1616
    intervalAccepted1616 (fun t => piece_le_psi ⟨1374,by decide +kernel⟩ t)
def piece1617 : AffinePiece := pieces[1375]'(by decide +kernel)
theorem intervalAccepted1617 : candidateIntervalCheck candidate1617 (8539/10000) (427/500) piece1617=true := by decide +kernel
noncomputable def cell1617 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1617 accepted1617 (8539/10000) (427/500) piece1617
    intervalAccepted1617 (fun t => piece_le_psi ⟨1375,by decide +kernel⟩ t)
def piece1618 : AffinePiece := pieces[1376]'(by decide +kernel)
theorem intervalAccepted1618 : candidateIntervalCheck candidate1618 (427/500) (8541/10000) piece1618=true := by decide +kernel
noncomputable def cell1618 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1618 accepted1618 (427/500) (8541/10000) piece1618
    intervalAccepted1618 (fun t => piece_le_psi ⟨1376,by decide +kernel⟩ t)
def piece1619 : AffinePiece := pieces[1377]'(by decide +kernel)
theorem intervalAccepted1619 : candidateIntervalCheck candidate1619 (8541/10000) (4271/5000) piece1619=true := by decide +kernel
noncomputable def cell1619 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1619 accepted1619 (8541/10000) (4271/5000) piece1619
    intervalAccepted1619 (fun t => piece_le_psi ⟨1377,by decide +kernel⟩ t)
def piece1620 : AffinePiece := pieces[1378]'(by decide +kernel)
theorem intervalAccepted1620 : candidateIntervalCheck candidate1620 (4271/5000) (8543/10000) piece1620=true := by decide +kernel
noncomputable def cell1620 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1620 accepted1620 (4271/5000) (8543/10000) piece1620
    intervalAccepted1620 (fun t => piece_le_psi ⟨1378,by decide +kernel⟩ t)
def piece1621 : AffinePiece := pieces[1379]'(by decide +kernel)
theorem intervalAccepted1621 : candidateIntervalCheck candidate1621 (8543/10000) (534/625) piece1621=true := by decide +kernel
noncomputable def cell1621 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1621 accepted1621 (8543/10000) (534/625) piece1621
    intervalAccepted1621 (fun t => piece_le_psi ⟨1379,by decide +kernel⟩ t)
def piece1622 : AffinePiece := pieces[1380]'(by decide +kernel)
theorem intervalAccepted1622 : candidateIntervalCheck candidate1622 (534/625) (1709/2000) piece1622=true := by decide +kernel
noncomputable def cell1622 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1622 accepted1622 (534/625) (1709/2000) piece1622
    intervalAccepted1622 (fun t => piece_le_psi ⟨1380,by decide +kernel⟩ t)
def piece1623 : AffinePiece := pieces[1381]'(by decide +kernel)
theorem intervalAccepted1623 : candidateIntervalCheck candidate1623 (1709/2000) (4273/5000) piece1623=true := by decide +kernel
noncomputable def cell1623 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1623 accepted1623 (1709/2000) (4273/5000) piece1623
    intervalAccepted1623 (fun t => piece_le_psi ⟨1381,by decide +kernel⟩ t)
def piece1624 : AffinePiece := pieces[1382]'(by decide +kernel)
theorem intervalAccepted1624 : candidateIntervalCheck candidate1624 (4273/5000) (8547/10000) piece1624=true := by decide +kernel
noncomputable def cell1624 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1624 accepted1624 (4273/5000) (8547/10000) piece1624
    intervalAccepted1624 (fun t => piece_le_psi ⟨1382,by decide +kernel⟩ t)
def piece1625 : AffinePiece := pieces[1383]'(by decide +kernel)
theorem intervalAccepted1625 : candidateIntervalCheck candidate1625 (8547/10000) (2137/2500) piece1625=true := by decide +kernel
noncomputable def cell1625 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1625 accepted1625 (8547/10000) (2137/2500) piece1625
    intervalAccepted1625 (fun t => piece_le_psi ⟨1383,by decide +kernel⟩ t)
def piece1626 : AffinePiece := pieces[1384]'(by decide +kernel)
theorem intervalAccepted1626 : candidateIntervalCheck candidate1626 (2137/2500) (8549/10000) piece1626=true := by decide +kernel
noncomputable def cell1626 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1626 accepted1626 (2137/2500) (8549/10000) piece1626
    intervalAccepted1626 (fun t => piece_le_psi ⟨1384,by decide +kernel⟩ t)
def piece1627 : AffinePiece := pieces[1385]'(by decide +kernel)
theorem intervalAccepted1627 : candidateIntervalCheck candidate1627 (8549/10000) (171/200) piece1627=true := by decide +kernel
noncomputable def cell1627 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1627 accepted1627 (8549/10000) (171/200) piece1627
    intervalAccepted1627 (fun t => piece_le_psi ⟨1385,by decide +kernel⟩ t)
def piece1628 : AffinePiece := pieces[1386]'(by decide +kernel)
theorem intervalAccepted1628 : candidateIntervalCheck candidate1628 (171/200) (8551/10000) piece1628=true := by decide +kernel
noncomputable def cell1628 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1628 accepted1628 (171/200) (8551/10000) piece1628
    intervalAccepted1628 (fun t => piece_le_psi ⟨1386,by decide +kernel⟩ t)
def piece1629 : AffinePiece := pieces[1387]'(by decide +kernel)
theorem intervalAccepted1629 : candidateIntervalCheck candidate1629 (8551/10000) (1069/1250) piece1629=true := by decide +kernel
noncomputable def cell1629 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1629 accepted1629 (8551/10000) (1069/1250) piece1629
    intervalAccepted1629 (fun t => piece_le_psi ⟨1387,by decide +kernel⟩ t)
def piece1630 : AffinePiece := pieces[1388]'(by decide +kernel)
theorem intervalAccepted1630 : candidateIntervalCheck candidate1630 (1069/1250) (8553/10000) piece1630=true := by decide +kernel
noncomputable def cell1630 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1630 accepted1630 (1069/1250) (8553/10000) piece1630
    intervalAccepted1630 (fun t => piece_le_psi ⟨1388,by decide +kernel⟩ t)
def piece1631 : AffinePiece := pieces[1389]'(by decide +kernel)
theorem intervalAccepted1631 : candidateIntervalCheck candidate1631 (8553/10000) (4277/5000) piece1631=true := by decide +kernel
noncomputable def cell1631 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate1631 accepted1631 (8553/10000) (4277/5000) piece1631
    intervalAccepted1631 (fun t => piece_le_psi ⟨1389,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell1616, cell1617, cell1618, cell1619, cell1620, cell1621, cell1622, cell1623, cell1624, cell1625, cell1626, cell1627, cell1628, cell1629, cell1630, cell1631]
theorem chainAccepted : spinCellChainCheck (4269/5000) (4277/5000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (4269/5000) (4277/5000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0101
