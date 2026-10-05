module

public import BecknerOnofri.SelectedMarginalCorrelation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Actual one-coordinate Fubini marginals and their Fourier coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped BigOperators
namespace BecknerOnofri.HighDim.ContinuousMarginal
open ContinuousGibbs

/-- The actual circle marginal, obtained by integrating all other coordinates. -/
def marginal {d : ℕ} (i : Fin (d+1)) (f : Space (d+1)) : C(UnitAddCircle,ℝ) where
  toFun s := ∫ x : Torus d,f (i.insertNth s x) ∂torusMeasure d
  continuous_toFun := by
    have hc : Continuous (fun p : UnitAddCircle×Torus d => f (i.insertNth p.1 p.2)) :=
      f.continuous.comp (continuous_fst.finInsertNth (A := fun _ => UnitAddCircle) i continuous_snd)
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ := torusMeasure d) hc
        (isCompact_univ : IsCompact (Set.univ : Set (Torus d)))

@[simp] theorem marginal_apply {d : ℕ} (i : Fin (d+1)) (f : Space (d+1)) (s : UnitAddCircle) :
    marginal i f s=∫ x : Torus d,f (i.insertNth s x) ∂torusMeasure d := rfl

theorem mFourier_single_int {d : ℕ} (i : Fin d) (n : ℤ) (x : Torus d) :
    UnitAddTorus.mFourier (Pi.single i n) x=_root_.fourier n (x i) := by
  classical
  change (∏ j,_root_.fourier ((Pi.single i n : Frequency d) j) (x j))=_
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem integral_insert {d : ℕ} (i : Fin (d+1)) (f : C(Torus (d+1),ℂ)) :
    (∫ p : UnitAddCircle×Torus d,f (i.insertNth p.1 p.2)
      ∂AddCircle.haarAddCircle.prod (torusMeasure d))=∫ x,f x ∂torusMeasure (d+1) := by
  have h := ((measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => AddCircle.haarAddCircle) i).symm
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) i)).integral_comp' f
  exact h

/-- Fubini identifies the true marginal coefficient with the corresponding axis coefficient. -/
theorem marginal_fourier {d : ℕ} (i : Fin (d+1)) (f : Space (d+1)) (n : ℤ) :
    _root_.fourierCoeff (fun s => (marginal i f s : ℂ)) n=fourierCoeff f (Pi.single i n) := by
  let g : C(Torus (d+1),ℂ) :=
    (UnitAddTorus.mFourier (-Pi.single i n))*⟨fun x => (f x:ℂ),by fun_prop⟩
  have hc : Continuous (fun p : UnitAddCircle×Torus d => g (i.insertNth p.1 p.2)) :=
    g.continuous.comp (continuous_fst.finInsertNth (A := fun _ => UnitAddCircle) i continuous_snd)
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := AddCircle.haarAddCircle.prod (torusMeasure d))
  calc
    _ = ∫ s : UnitAddCircle, ∫ x : Torus d, g (i.insertNth s x)
        ∂torusMeasure d ∂AddCircle.haarAddCircle := by
      unfold _root_.fourierCoeff
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => by
        simp only [marginal_apply,← integral_complex_ofReal,smul_eq_mul,← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by
          change _root_.fourier (-n) s*(f (i.insertNth s x):ℂ)=
            UnitAddTorus.mFourier (-Pi.single i n) (i.insertNth s x)*(f (i.insertNth s x):ℂ)
          congr 1
          rw [show -(Pi.single i n : Frequency (d+1))=Pi.single i (-n) from by ext j; by_cases hj : j=i <;> simp [Pi.single_apply,hj],
            mFourier_single_int,Fin.insertNth_apply_same]))
    _ = ∫ p : UnitAddCircle×Torus d,g (i.insertNth p.1 p.2)
        ∂AddCircle.haarAddCircle.prod (torusMeasure d) := (integral_prod _ hi).symm
    _ = _ := integral_insert i g

/-- Parseval on the actual circle, without introducing a formal marginal coefficient sequence. -/
theorem circle_parseval (f : C(UnitAddCircle,ℝ)) :
    HasSum (fun n : ℤ => ‖_root_.fourierCoeff (fun s => (f s:ℂ)) n‖^2)
      (∫ s,(f s)^2 ∂AddCircle.haarAddCircle) := by
  let g : C(UnitAddCircle,ℂ) := ⟨fun s => (f s:ℂ),by fun_prop⟩
  have h := _root_.hasSum_sq_fourierCoeff (g.toLp 2 AddCircle.haarAddCircle ℂ)
  simp_rw [_root_.fourierCoeff_toLp] at h
  convert! h using 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toAEEqFun AddCircle.haarAddCircle g] with s hs
  change (f s)^2=‖(g.toLp 2 AddCircle.haarAddCircle ℂ) s‖^2
  change (g.toLp 2 AddCircle.haarAddCircle ℂ) s=g s at hs
  rw [hs]
  simp [g,Complex.norm_real,Real.norm_eq_abs]

/-- Actual continuous circle functions are determined by their Fourier coefficients. -/
theorem circle_fourier_ext (f g : C(UnitAddCircle,ℝ))
    (h : ∀ n : ℤ,_root_.fourierCoeff (fun s => (f s:ℂ)) n=
      _root_.fourierCoeff (fun s => (g s:ℂ)) n) : f=g := by
  let fC : C(UnitAddCircle,ℂ) := ⟨fun s => (f s:ℂ),by fun_prop⟩
  let gC : C(UnitAddCircle,ℂ) := ⟨fun s => (g s:ℂ),by fun_prop⟩
  have he : fC=gC := by
    apply ContinuousMap.toLp_injective 2 AddCircle.haarAddCircle ℂ
    apply _root_.fourierBasis.repr.injective
    ext n
    rw [_root_.fourierBasis_repr,_root_.fourierBasis_repr,
      _root_.fourierCoeff_toLp,_root_.fourierCoeff_toLp]
    exact h n
  ext s
  exact Complex.ofReal_injective (congrArg (fun F : C(UnitAddCircle,ℂ) => F s) he)

#print axioms marginal_fourier
#print axioms circle_parseval
end BecknerOnofri.HighDim.ContinuousMarginal
