import BecknerOnofri.Friedrichs.FormSubmodule
import BecknerOnofri.Friedrichs.SpatialOperatorProperties
import Mathlib.Topology.MetricSpace.Cauchy

/-! Closedness of the independently defined spatial weak operator graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology
namespace BecknerOnofri.Friedrichs.SpatialForm

def liftedGraph (m : ℕ) (u : EnergySpace) (g : H) : Prop :=
  u∈formClosure m ∧ ∀ w∈formClosure m,formPairing u w=inner ℝ g w.1

lemma liftedGraph_sub {m : ℕ} {u v : EnergySpace} {g h : H}
    (hu : liftedGraph m u g) (hv : liftedGraph m v h) : liftedGraph m (u-v) (g-h) := by
  refine ⟨(closedFormSubmodule m).sub_mem hu.1 hv.1,?_⟩
  intro w hw
  have h1 := hu.2 w hw
  have h2 := hv.2 w hw
  dsimp [formPairing] at *
  simp only [Prod.fst_sub,Prod.snd_sub,inner_sub_left]
  linarith

lemma liftedGraph_component_bounds {m : ℕ} {u : EnergySpace} {g : H}
    (hu : liftedGraph m u g) :
    ‖u.2.1‖ ≤ ‖u.1‖+‖g‖ ∧ ‖u.2.2‖ ≤ ‖u.1‖+‖g‖ := by
  have he := hu.2 u hu.1
  simp only [formPairing,real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm g u.1
  have h0 := norm_nonneg u.1
  have hg := norm_nonneg g
  have hp := norm_nonneg u.2.1
  have hv := norm_nonneg u.2.2
  constructor <;> nlinarith [sq_nonneg (‖u.2.1‖),sq_nonneg (‖u.2.2‖),sq_nonneg (‖u.1‖-‖g‖)]

lemma cauchySeq_of_graph_bound {a b p : ℕ → H} (ha : CauchySeq a) (hb : CauchySeq b)
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

theorem operatorGraph_of_tendsto {m : ℕ} {f g : ℕ → H} {f₀ g₀ : H}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (h : ∀ n,operatorGraph m (f n) (g n)) : operatorGraph m f₀ g₀ := by
  choose p v hc ht using fun n => (operatorGraph_iff_closed_tests m (f n) (g n)).mp (h n)
  have hLift (n : ℕ) : liftedGraph m (f n,(p n,v n)) (g n) := ⟨hc n,ht n⟩
  have hpC : CauchySeq p := cauchySeq_of_graph_bound hf.cauchySeq hg.cauchySeq
    (fun i j => (liftedGraph_component_bounds (liftedGraph_sub (hLift i) (hLift j))).1)
  have hvC : CauchySeq v := cauchySeq_of_graph_bound hf.cauchySeq hg.cauchySeq
    (fun i j => (liftedGraph_component_bounds (liftedGraph_sub (hLift i) (hLift j))).2)
  obtain ⟨p₀,hp⟩ := cauchySeq_tendsto_of_complete hpC
  obtain ⟨v₀,hv⟩ := cauchySeq_tendsto_of_complete hvC
  have hconv : Tendsto (fun n => (f n,(p n,v n))) atTop (𝓝 (f₀,(p₀,v₀))) := by
    simpa only [← nhds_prod_eq] using hf.prodMk (hp.prodMk hv)
  have hclosed : (f₀,(p₀,v₀))∈formClosure m :=
    isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall hc)
  apply (operatorGraph_iff_closed_tests m f₀ g₀).mpr
  refine ⟨p₀,v₀,hclosed,?_⟩
  intro w hw
  have hleft : Tendsto (fun n => formPairing (f n,(p n,v n)) w) atTop
      (𝓝 (formPairing (f₀,(p₀,v₀)) w)) :=
    (hp.inner tendsto_const_nhds).add (hv.inner tendsto_const_nhds)
  have hright : Tendsto (fun n => inner ℝ (g n) w.1) atTop (𝓝 (inner ℝ g₀ w.1)) :=
    hg.inner tendsto_const_nhds
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (ht n w hw).symm))

#print axioms operatorGraph_of_tendsto
end BecknerOnofri.Friedrichs.SpatialForm
