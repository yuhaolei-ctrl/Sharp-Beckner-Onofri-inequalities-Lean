module

public import BecknerOnofri.SpinCellAssembly
public import BecknerOnofri.EntropyScalarCertificate.Minorant
public import BecknerOnofri.EntropySpinCertificate.Candidates0001

@[expose] public section
namespace BecknerOnofri.HighDim.Spin.IntervalBatch0001
open CandidateBatch0001 ScalarCertificate ScalarCertificate.CertifiedMinorant
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def piece0016 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0016 : candidateIntervalCheck candidate0016 (633/10000) (1267/20000) piece0016=true := by decide +kernel
noncomputable def cell0016 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0016 accepted0016 (633/10000) (1267/20000) piece0016
    intervalAccepted0016 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0017 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0017 : candidateIntervalCheck candidate0017 (1267/20000) (317/5000) piece0017=true := by decide +kernel
noncomputable def cell0017 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0017 accepted0017 (1267/20000) (317/5000) piece0017
    intervalAccepted0017 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0018 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0018 : candidateIntervalCheck candidate0018 (317/5000) (1269/20000) piece0018=true := by decide +kernel
noncomputable def cell0018 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0018 accepted0018 (317/5000) (1269/20000) piece0018
    intervalAccepted0018 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0019 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0019 : candidateIntervalCheck candidate0019 (1269/20000) (127/2000) piece0019=true := by decide +kernel
noncomputable def cell0019 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0019 accepted0019 (1269/20000) (127/2000) piece0019
    intervalAccepted0019 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0020 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0020 : candidateIntervalCheck candidate0020 (127/2000) (1271/20000) piece0020=true := by decide +kernel
noncomputable def cell0020 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0020 accepted0020 (127/2000) (1271/20000) piece0020
    intervalAccepted0020 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0021 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0021 : candidateIntervalCheck candidate0021 (1271/20000) (159/2500) piece0021=true := by decide +kernel
noncomputable def cell0021 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0021 accepted0021 (1271/20000) (159/2500) piece0021
    intervalAccepted0021 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0022 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0022 : candidateIntervalCheck candidate0022 (159/2500) (1273/20000) piece0022=true := by decide +kernel
noncomputable def cell0022 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0022 accepted0022 (159/2500) (1273/20000) piece0022
    intervalAccepted0022 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0023 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0023 : candidateIntervalCheck candidate0023 (1273/20000) (637/10000) piece0023=true := by decide +kernel
noncomputable def cell0023 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0023 accepted0023 (1273/20000) (637/10000) piece0023
    intervalAccepted0023 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0024 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0024 : candidateIntervalCheck candidate0024 (637/10000) (51/800) piece0024=true := by decide +kernel
noncomputable def cell0024 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0024 accepted0024 (637/10000) (51/800) piece0024
    intervalAccepted0024 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0025 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0025 : candidateIntervalCheck candidate0025 (51/800) (319/5000) piece0025=true := by decide +kernel
noncomputable def cell0025 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0025 accepted0025 (51/800) (319/5000) piece0025
    intervalAccepted0025 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0026 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0026 : candidateIntervalCheck candidate0026 (319/5000) (1277/20000) piece0026=true := by decide +kernel
noncomputable def cell0026 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0026 accepted0026 (319/5000) (1277/20000) piece0026
    intervalAccepted0026 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0027 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0027 : candidateIntervalCheck candidate0027 (1277/20000) (639/10000) piece0027=true := by decide +kernel
noncomputable def cell0027 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0027 accepted0027 (1277/20000) (639/10000) piece0027
    intervalAccepted0027 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0028 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0028 : candidateIntervalCheck candidate0028 (639/10000) (1279/20000) piece0028=true := by decide +kernel
noncomputable def cell0028 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0028 accepted0028 (639/10000) (1279/20000) piece0028
    intervalAccepted0028 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0029 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0029 : candidateIntervalCheck candidate0029 (1279/20000) (8/125) piece0029=true := by decide +kernel
noncomputable def cell0029 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0029 accepted0029 (1279/20000) (8/125) piece0029
    intervalAccepted0029 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0030 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0030 : candidateIntervalCheck candidate0030 (8/125) (1281/20000) piece0030=true := by decide +kernel
noncomputable def cell0030 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0030 accepted0030 (8/125) (1281/20000) piece0030
    intervalAccepted0030 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
def piece0031 : AffinePiece := pieces[0]'(by decide +kernel)
theorem intervalAccepted0031 : candidateIntervalCheck candidate0031 (1281/20000) (641/10000) piece0031=true := by decide +kernel
noncomputable def cell0031 : CertifiedSpinCell psi :=
  spinCellOfCandidate psi candidate0031 accepted0031 (1281/20000) (641/10000) piece0031
    intervalAccepted0031 (fun t => piece_le_psi ⟨0,by decide +kernel⟩ t)
noncomputable def cells : List (CertifiedSpinCell psi) := [cell0016, cell0017, cell0018, cell0019, cell0020, cell0021, cell0022, cell0023, cell0024, cell0025, cell0026, cell0027, cell0028, cell0029, cell0030, cell0031]
theorem chainAccepted : spinCellChainCheck (633/10000) (641/10000) cells=true := by decide +kernel
noncomputable def block : CertifiedSpinCell psi := spinCellOfChain psi (633/10000) (641/10000) cells chainAccepted
#print axioms block
end BecknerOnofri.HighDim.Spin.IntervalBatch0001
