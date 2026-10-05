module

public import BecknerOnofri.SpinDefinitions
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! Actual binary-spin configurations, count law, and permutation symmetry. -/
noncomputable section
open scoped BigOperators
namespace BecknerOnofri.HighDim.Spin

abbrev Configuration := Finset (Fin 12)
def plusCount (σ : Configuration) : Count :=
  ⟨σ.card,Nat.lt_succ_of_le (by simpa using Finset.card_le_card (Finset.subset_univ σ))⟩
def countClass (j : Count) : Finset Configuration :=
  (Finset.univ : Finset (Fin 12)).powersetCard j.val
def countLaw (ν : Configuration → ℝ) (j : Count) : ℝ :=
  ∑ σ ∈ countClass j,ν σ
def Exchangeable (ν : Configuration → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin 12)) (σ : Configuration),ν (σ.map π.toEmbedding)=ν σ

def firstCoordinates (s : Order) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => i.val<s.val+1)
def jointSpinQ (S : Finset (Fin 12)) (σ : Configuration) : ℚ :=
  ∏ i ∈ σᶜ,if i∈S then (-1:ℚ) else 1

end BecknerOnofri.HighDim.Spin
