module

public import BecknerOnofri.Friedrichs.SpatialEigenvectors
public import BecknerOnofri.Friedrichs.SpatialGraphLinear

@[expose] public section

/-! Exact one-dimensional identification of the spatial weak graph with the
Jacobi spectral graph. Both directions are proved; spatial form membership
is obtained by closure of finite actual eigenfunction sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Friedrichs.SpatialForm
open Legacy.BecknerOnofri.JacobiEigenfunctions (eigenvector eigenvalue normalizedVector
  normSquared hilbertBasis hilbertBasis_apply)

lemma normalizedVector_operatorGraph {m : ℕ} (hm : 0<m) (n : ℕ) :
    operatorGraph m (normalizedVector m n) (eigenvalue m n • normalizedVector m n) := by
  have h := operatorGraph_smul (eigenvector_operatorGraph hm n) (Real.sqrt (normSquared m n))⁻¹
  simpa only [normalizedVector,smul_smul,mul_comm] using h

lemma operatorGraph_repr {m : ℕ} (hm : 0<m) {f g : H} (h : operatorGraph m f g) (n : ℕ) :
    (hilbertBasis hm).repr g n=eigenvalue m n*(hilbertBasis hm).repr f n := by
  have he := operatorGraph_symmetric h (normalizedVector_operatorGraph hm n)
  simpa only [HilbertBasis.repr_apply_apply,hilbertBasis_apply,real_inner_comm,inner_smul_right] using he

theorem operatorGraph_iff_repr {m : ℕ} (hm : 0<m) (f g : H) :
    operatorGraph m f g ↔ ∀ n,(hilbertBasis hm).repr g n=eigenvalue m n*(hilbertBasis hm).repr f n := by
  constructor
  · exact fun h n => operatorGraph_repr hm h n
  · intro h
    let b := hilbertBasis hm
    let fN (N : ℕ) : H := ∑ n∈Finset.range N,b.repr f n • b n
    let gN (N : ℕ) : H := ∑ n∈Finset.range N,b.repr g n • b n
    have hf : Tendsto fN atTop (𝓝 f) := (b.hasSum_repr f).comp tendsto_finset_range
    have hg : Tendsto gN atTop (𝓝 g) := (b.hasSum_repr g).comp tendsto_finset_range
    apply operatorGraph_of_tendsto hf hg
    intro N
    apply operatorGraph_sum
    intro n hn
    have he := operatorGraph_smul (normalizedVector_operatorGraph hm n) (b.repr f n)
    simpa only [b,hilbertBasis_apply,smul_smul,h n,mul_comm] using he

#print axioms operatorGraph_iff_repr
end BecknerOnofri.Friedrichs.SpatialForm
