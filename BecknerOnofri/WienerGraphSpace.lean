import BecknerOnofri.LocalElevenCore.WienerAlgebraBounds
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! A complete space for continuous functions with polynomially weighted
summable Fourier coefficients. The graph norm keeps the actual function and
its weighted coefficients together; completeness is proved from a closed
linear constraint, rather than assumed for the stronger topology. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.RadialWiener

abbrev Coefficients (d : ℕ) := lp (fun _ : Frequency d => ℂ) 1
abbrev Ambient (d : ℕ) := Space d × Coefficients d

def graph (d m : ℕ) : Submodule ℝ (Ambient d) where
  carrier := {x | ∀ k, x.2 k=(radialWeight m k : ℝ) • coefficient k x.1}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro x y hx hy k
    change x.2 k+y.2 k=radialWeight m k • coefficient k (x.1+y.1)
    rw [map_add,smul_add,hx k,hy k]
  smul_mem' := by
    intro c x hx k
    change c • x.2 k=radialWeight m k • coefficient k (c • x.1)
    rw [map_smul,hx k,smul_comm]

theorem graph_isClosed (d m : ℕ) : IsClosed (graph d m : Set (Ambient d)) := by
  change IsClosed {x : Ambient d | ∀ k,x.2 k=radialWeight m k • coefficient k x.1}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq
    ((lp.evalCLM ℝ (fun _ : Frequency d => ℂ) 1 k).continuous.comp continuous_snd)
    (((coefficient k).continuous.comp continuous_fst).const_smul (radialWeight m k))

instance graph_completeSpace (d m : ℕ) : CompleteSpace (graph d m) := by
  haveI : IsClosed (graph d m : Set (Ambient d)) := graph_isClosed d m
  infer_instance

/-- The continuous function is a genuine bounded linear projection of the
complete weighted graph space. -/
def toContinuous (d m : ℕ) : graph d m →L[ℝ] Space d :=
  (ContinuousLinearMap.fst ℝ (Space d) (Coefficients d)).comp (graph d m).subtypeL

@[simp] lemma toContinuous_apply {d m : ℕ} (x : graph d m) : toContinuous d m x=x.val.1 := rfl

theorem toContinuous_injective (d m : ℕ) : Function.Injective (toContinuous d m) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext h
  apply lp.ext
  funext k
  change x.val.2 k=y.val.2 k
  rw [x.property k,y.property k]
  change radialWeight m k • coefficient k (toContinuous d m x)=
    radialWeight m k • coefficient k (toContinuous d m y)
  rw [h]

#print axioms graph_isClosed
#print axioms toContinuous_injective
end BecknerOnofri.HighDim.WienerGraph
