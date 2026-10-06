module

public import BecknerOnofri.SimultaneousOrbitCompact
public import BecknerOnofri.PolarizationUniformL1
public import BecknerOnofri.BilinearPairingL1Limit
public import BecknerOnofri.PolarizationL1Properties

@[expose] public section

/-! Order, L1 contraction, and bounded-kernel comparison on the actual
simultaneous orbit and its uniform closure. -/
noncomputable section
open MeasureTheory Set Filter Legacy.TorusEndpoint
open scoped Topology NNReal BoundedContinuousFunction
namespace BecknerOnofri.PolarizationL1
open Legacy.BecknerOnofri.CoordinatePolarization BilinearPolarization

theorem PairOrbit.mono {d : ℕ} {f g u v : Torus d → ℝ}
    (h : PairOrbit f g u v) (hfg : ∀ x,f x≤g x) : ∀ x,u x≤v x := by
  induction h with
  | refl => exact hfg
  | step h i a ih => exact polarize_mono i a ih

theorem PairOrbit.l1_contraction {d : ℕ} {f g u v : Torus d → ℝ}
    (h : PairOrbit f g u v)
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) :
    (∫ x,‖u x-v x‖ ∂torusMeasure d)≤∫ x,‖f x-g x‖ ∂torusMeasure d := by
  induction h with
  | refl => exact le_refl _
  | @step u v h i a ih =>
    have hu := h.left.identDistrib hf.aestronglyMeasurable
    have hv := h.right.identDistrib hg.aestronglyMeasurable
    have hnew : (∫ x,‖polarize i a u x-polarize i a v x‖ ∂torusMeasure d)≤
        ∫ x,‖u x-v x‖ ∂torusMeasure d := by
      simpa only [Real.norm_eq_abs] using
        polarize_l1_contraction i a u v (hu.integrable_iff.mpr hf) (hv.integrable_iff.mpr hg)
    exact hnew.trans ih

theorem PairOrbit.pairing_le {d : ℕ} {f g u v : Torus d → ℝ}
    (h : PairOrbit f g u v)
    (Q : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry Q))
    {C : ℝ} (hC : ∀ x y,‖Q x y‖≤C)
    (hQ : ∀ i a x y,Q (reflection i a x) (reflection i a y)=Q x y)
    (hmono : ∀ i a,∀ x∈halfTorus i a,∀ y∈halfTorus i a,Q x (reflection i a y)≤Q x y)
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) :
    pairing Q f g≤pairing Q u v := by
  induction h with
  | refl => exact le_refl _
  | @step u v h i a ih =>
    exact ih.trans (pairing_polarize_le_bounded i a Q hm hC (hQ i a) (hmono i a)
      ((h.left.identDistrib hf.aestronglyMeasurable).integrable_iff.mpr hf)
      ((h.right.identDistrib hg.aestronglyMeasurable).integrable_iff.mpr hg))

theorem pair_closure_mono {d : ℕ} {f g : Torus d → ℝ}
    {p : (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)} (hp : p∈closure (boundedPairOrbit f g))
    (hfg : ∀ x,f x≤g x) : ∀ x,p.1 x≤p.2 x := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
  intro x
  have h1 := (ContinuousEvalConst.continuous_eval_const x).tendsto p.1 |>.comp htu.fst_nhds
  have h2 := (ContinuousEvalConst.continuous_eval_const x).tendsto p.2 |>.comp htu.snd_nhds
  exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall
    (fun n => PairOrbit.mono (hu n) hfg x))

lemma integral_norm_sub_triangle {d : ℕ} {f g h : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    (hh : Integrable h (torusMeasure d)) :
    (∫ x,‖f x-h x‖ ∂torusMeasure d)≤
      (∫ x,‖f x-g x‖ ∂torusMeasure d)+(∫ x,‖g x-h x‖ ∂torusMeasure d) := by
  calc
    _ ≤ ∫ x,(‖f x-g x‖+‖g x-h x‖) ∂torusMeasure d :=
      integral_mono ((hf.sub hh).norm) (((hf.sub hg).norm).add ((hg.sub hh).norm))
        (fun x => norm_sub_le_norm_sub_add_norm_sub (f x) (g x) (h x))
    _ = _ := integral_add ((hf.sub hg).norm) ((hg.sub hh).norm)

theorem pair_closure_l1_contraction {d : ℕ} {f g : Torus d → ℝ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    {p : (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)} (hp : p∈closure (boundedPairOrbit f g)) :
    (∫ x,‖p.1 x-p.2 x‖ ∂torusMeasure d)≤∫ x,‖f x-g x‖ ∂torusMeasure d := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
  have h1 := bounded_tendsto_l1 htu.fst_nhds
  have h2 := bounded_tendsto_l1 htu.snd_nhds
  have hb (n : ℕ) : (∫ x,‖p.1 x-p.2 x‖ ∂torusMeasure d)≤
      (∫ x,‖(u n).1 x-p.1 x‖ ∂torusMeasure d)+
      (∫ x,‖f x-g x‖ ∂torusMeasure d)+(∫ x,‖(u n).2 x-p.2 x‖ ∂torusMeasure d) := by
    have ha := integral_norm_sub_triangle (p.1.integrable _) ((u n).1.integrable _) (p.2.integrable _)
    have hb := integral_norm_sub_triangle ((u n).1.integrable _) ((u n).2.integrable _) (p.2.integrable _)
    have hc := PairOrbit.l1_contraction (hu n) hf hg
    have he : (∫ x,‖p.1 x-(u n).1 x‖ ∂torusMeasure d)=
        ∫ x,‖(u n).1 x-p.1 x‖ ∂torusMeasure d :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => norm_sub_rev _ _))
    rw [he] at ha
    linarith
  have ht := (h1.add (tendsto_const_nhds (x := ∫ x,‖f x-g x‖ ∂torusMeasure d))).add h2
  simp only [zero_add,add_zero] at ht
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall hb)

theorem pair_closure_pairing_le {d : ℕ} {f g : Torus d → ℝ}
    (Q : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry Q))
    {C : ℝ} (hC : ∀ x y,‖Q x y‖≤C)
    (hQ : ∀ i a x y,Q (reflection i a x) (reflection i a y)=Q x y)
    (hmono : ∀ i a,∀ x∈halfTorus i a,∀ y∈halfTorus i a,Q x (reflection i a y)≤Q x y)
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d))
    {p : (Torus d →ᵇ ℝ) × (Torus d →ᵇ ℝ)} (hp : p∈closure (boundedPairOrbit f g)) :
    pairing Q f g≤pairing Q p.1 p.2 := by
  obtain ⟨u,hu,htu⟩ := mem_closure_iff_seq_limit.mp hp
  have ht := pairing_l1_limit atTop Q hm hC (fun n => (u n).1) (fun n => (u n).2) p.1 p.2
    (fun n => (u n).1.integrable _) (fun n => (u n).2.integrable _)
    (p.1.integrable _) (p.2.integrable _) (bounded_tendsto_l1 htu.fst_nhds) (bounded_tendsto_l1 htu.snd_nhds)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall
    (fun n => PairOrbit.pairing_le (hu n) Q hm hC hQ hmono hf hg))

#print axioms pair_closure_mono
#print axioms pair_closure_l1_contraction
#print axioms pair_closure_pairing_le
end BecknerOnofri.PolarizationL1
