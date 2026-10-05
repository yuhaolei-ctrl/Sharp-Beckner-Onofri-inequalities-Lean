module

public import BecknerOnofri.AngularRealPowerDomain

@[expose] public section

/-! Finite spectral polynomials converge in the graph topology of every
positive real power. This is the closed-operator limit step in the manuscript;
the independent identification with the Friedrichs form is still required. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace BecknerOnofri.AngularRealPower
open Legacy.BecknerOnofri JacobiTensor JacobiTensorSpectrum

/-- Simultaneous finite polynomial approximation of a vector and its image. -/
theorem polynomial_core {d : ℕ} (α : Index d) (hα : α≠0) (s : ℝ) (hs : 0<s)
    (u v : TensorL2 d) (h : PowerGraph α hα s hs u v) :
    (∀ S : Finset (Index d), PowerGraph α hα s hs
      (∑ n ∈ S,(hilbertBasis α).repr u n • tensorVector α n)
      (∑ n ∈ S,(hilbertBasis α).repr v n • tensorVector α n)) ∧
    Tendsto (fun S : Finset (Index d) =>
      (∑ n ∈ S,(hilbertBasis α).repr u n • tensorVector α n,
       ∑ n ∈ S,(hilbertBasis α).repr v n • tensorVector α n))
      atTop (𝓝 (u,v)) := by
  constructor
  · intro S
    change inversePower α hα s hs _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_smul,inverse_tensorVector,smul_smul,powerGraph_repr α hα s hs h n]
    have hp : 0 < tensorEigenvalue α n := (positiveSpectrum α hα).value_pos n
    congr 1
    calc
      _ = ((tensorEigenvalue α n)^s*(tensorEigenvalue α n)^(-s))*
          (hilbertBasis α).repr u n := by ring
      _ = _ := by rw [← Real.rpow_add hp]; simp
  · have hu := (hilbertBasis α).hasSum_repr u
    have hv := (hilbertBasis α).hasSum_repr v
    simp only [hilbertBasis_apply] at hu hv
    exact hu.prodMk_nhds hv

#print axioms polynomial_core
end BecknerOnofri.AngularRealPower
