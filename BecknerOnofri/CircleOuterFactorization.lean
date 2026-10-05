import BecknerOnofri.CircleOuterWeighted

/-! A normalized positive even circle density with one absolutely summable
weighted Fourier moment of its logarithm has the actual real Hardy factor and
autocorrelations needed by the manuscript. Smoothness-to-summability and the
Fisher identity remain separate analytic steps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint Legacy.BecknerOnofri.WeightedWiener

theorem probability_outer_representation (p : Torus 1 → ℝ)
    (hp : Continuous p) (hpos : ∀ x,0<p x) (he : ∀ x,p (-x)=p x)
    (hm : (∫ x,p x ∂torusMeasure 1)=1)
    (hlog : Summable (fun k => linearWeight k*
      ‖UnitAddTorus.mFourierCoeff (fun x => (Real.log (p x):ℂ)) k‖)) :
    ∃ f : C(Torus 1,ℂ), ∃ u : CircleHardy.Space,
      (∀ x,Complex.normSq (f x)=p x) ∧ ‖u‖=1 ∧
      Summable (fun n : ℕ => (n:ℝ)*(u n)^2) ∧
      Summable (fun k => ‖UnitAddTorus.mFourierCoeff f k‖) ∧
      (∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ))) ∧
      (∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) ∧
      ∀ n : ℕ,CircleHardy.moment u n=
        (UnitAddTorus.mFourierCoeff (fun x => (p x:ℂ)) (fun _ => (n:ℤ))).re := by
  let g : Torus 1 → ℝ := fun x => Real.log (p x)
  have hg : Continuous g := hp.log (fun x => (hpos x).ne')
  have hge (x : Torus 1) : g (-x)=g x := by dsimp only [g]; rw [he]
  have hs : Summable (fun k => ‖UnitAddTorus.mFourierCoeff (fun x => (g x:ℂ)) k‖) :=
    summable_norm linearWeight_isWeight hlog
  obtain ⟨f,hf,hfs,hfr,hfn,hfw⟩ := logarithm_outer_exists (0:Fin 1) g hg hge hs
  have hfp (x : Torus 1) : Complex.normSq (f x)=p x := by
    rw [hf]
    exact Real.exp_log (hpos x)
  have hfm : (∫ x,Complex.normSq (f x) ∂torusMeasure 1)=1 := by
    simpa only [hfp] using hm
  obtain ⟨u,hu,huc⟩ := hardy_unit_vector f hfr hfn hfm
  have hE := hardy_weighted_energy f u hu huc (hfw linearWeight linearWeight_isWeight hlog)
  refine ⟨f,u,hfp,hu,hE,hfs,huc,hfn,?_⟩
  intro n
  have h := hardy_moment_eq_density_coefficient f u huc hfn n
  simpa only [hfp] using h

#print axioms probability_outer_representation
end BecknerOnofri.HighDim.CircleOuter
