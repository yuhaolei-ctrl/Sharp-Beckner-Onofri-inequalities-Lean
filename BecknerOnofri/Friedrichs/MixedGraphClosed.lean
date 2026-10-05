import BecknerOnofri.Friedrichs.MixedGraphLinear
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Sequences

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace BecknerOnofri.Friedrichs.MixedSpatial

def liftedGraph {d : ℕ} (α : MultiIndex d) (v : EnergySpace α) (g : H α) : Prop :=
  v∈formClosure α ∧ ∀ w∈formClosure α,formPairing v w=inner ℝ g w.1

lemma liftedGraph_sub {d : ℕ} {α : MultiIndex d} {u v : EnergySpace α} {g h : H α}
    (hu : liftedGraph α u g) (hv : liftedGraph α v h) : liftedGraph α (u-v) (g-h) := by
  refine ⟨(closedFormSubmodule α).sub_mem hu.1 hv.1,?_⟩
  intro w hw
  have he : formPairing (u-v) w=formPairing u w-formPairing v w := by
    rw [sub_eq_add_neg,← neg_one_smul ℝ v,formPairing_add_left,formPairing_smul_left]
    ring
  rw [he,hu.2 w hw,hv.2 w hw,inner_sub_left]

lemma liftedGraph_component_bounds {d : ℕ} {α : MultiIndex d} {u : EnergySpace α} {g : H α}
    (hu : liftedGraph α u g) (i : Fin d) :
    ‖u.2.1 i‖ ≤ ‖u.1‖+‖g‖ ∧ ‖u.2.2 i‖ ≤ ‖u.1‖+‖g‖ := by
  have he := hu.2 u hu.1
  simp only [formPairing,real_inner_self_eq_norm_sq] at he
  have hle : ‖u.2.1 i‖^2+‖u.2.2 i‖^2 ≤ inner ℝ g u.1 := by
    rw [← he]
    exact Finset.single_le_sum (fun j hj => add_nonneg (sq_nonneg (‖u.2.1 j‖))
      (sq_nonneg (‖u.2.2 j‖))) (Finset.mem_univ i)
  have hi := real_inner_le_norm g u.1
  have h0 := norm_nonneg u.1
  have hg := norm_nonneg g
  have hp := norm_nonneg (u.2.1 i)
  have hv := norm_nonneg (u.2.2 i)
  constructor <;> nlinarith [sq_nonneg (‖u.2.1 i‖),sq_nonneg (‖u.2.2 i‖),sq_nonneg (‖u.1‖-‖g‖)]

lemma cauchySeq_of_graph_bound {E : Type*} [NormedAddCommGroup E]
    {a b p : ℕ → E} (ha : CauchySeq a) (hb : CauchySeq b)
    (hp : ∀ i j,‖p i-p j‖ ≤ ‖a i-a j‖+‖b i-b j‖) : CauchySeq p := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp ha (ε/2) (half_pos hε)
  obtain ⟨M,hM⟩ := Metric.cauchySeq_iff.mp hb (ε/2) (half_pos hε)
  refine ⟨max N M,?_⟩
  intro i hi j hj
  have h1 := hN i (le_trans (le_max_left _ _) hi) j (le_trans (le_max_left _ _) hj)
  have h2 := hM i (le_trans (le_max_right _ _) hi) j (le_trans (le_max_right _ _) hj)
  rw [dist_eq_norm] at h1 h2 ⊢
  exact (hp i j).trans_lt (by linarith)

theorem operatorGraph_of_tendsto {d : ℕ} {α : MultiIndex d} {f g : ℕ → H α} {f₀ g₀ : H α}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (h : ∀ n,operatorGraph α (f n) (g n)) : operatorGraph α f₀ g₀ := by
  choose u hu hc ht using h
  have hLift (n : ℕ) : liftedGraph α (u n) (g n) := ⟨hc n,ht n⟩
  have hpC (i : Fin d) : CauchySeq (fun n => (u n).2.1 i) :=
    cauchySeq_of_graph_bound hf.cauchySeq hg.cauchySeq (fun n m => by
      simpa only [Prod.fst_sub,Prod.snd_sub,Pi.sub_apply,hu] using
        (liftedGraph_component_bounds (liftedGraph_sub (hLift n) (hLift m)) i).1)
  have hvC (i : Fin d) : CauchySeq (fun n => (u n).2.2 i) :=
    cauchySeq_of_graph_bound hf.cauchySeq hg.cauchySeq (fun n m => by
      simpa only [Prod.fst_sub,Prod.snd_sub,Pi.sub_apply,hu] using
        (liftedGraph_component_bounds (liftedGraph_sub (hLift n) (hLift m)) i).2)
  choose p₀ hp using fun i => cauchySeq_tendsto_of_complete (hpC i)
  choose v₀ hv using fun i => cauchySeq_tendsto_of_complete (hvC i)
  have hconv : Tendsto u atTop (𝓝 (f₀,(p₀,v₀))) := by
    have hp' := tendsto_pi_nhds.mpr hp
    have hv' := tendsto_pi_nhds.mpr hv
    have hf' : Tendsto (fun n => (u n).1) atTop (𝓝 f₀) := by simpa only [hu] using hf
    simpa only [← nhds_prod_eq] using hf'.prodMk (hp'.prodMk hv')
  have hclosed : (f₀,(p₀,v₀))∈formClosure α :=
    isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall hc)
  refine ⟨(f₀,(p₀,v₀)),rfl,hclosed,?_⟩
  intro w hw
  have hl : Tendsto (fun n => formPairing (u n) w) atTop
      (𝓝 (formPairing (f₀,(p₀,v₀)) w)) := by
    have hh : Continuous (fun v : EnergySpace α => formPairing v w) := by
      simpa only [formPairing_comm] using formPairing_continuous_right w
    exact hh.continuousAt.tendsto.comp hconv
  have hr : Tendsto (fun n => inner ℝ (g n) w.1) atTop (𝓝 (inner ℝ g₀ w.1)) :=
    hg.inner tendsto_const_nhds
  exact tendsto_nhds_unique hl (hr.congr (fun n => (ht n w hw).symm))

theorem operatorGraph_isClosed {d : ℕ} (α : MultiIndex d) :
    IsClosed {p : H α × H α | operatorGraph α p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro u p hu hup
  exact operatorGraph_of_tendsto ((continuous_fst.tendsto p).comp hup)
    ((continuous_snd.tendsto p).comp hup) hu

#print axioms operatorGraph_isClosed
#print axioms operatorGraph_of_tendsto
end BecknerOnofri.Friedrichs.MixedSpatial
