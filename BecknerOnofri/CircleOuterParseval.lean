module

public import BecknerOnofri.CircleOuterLogarithm
public import BecknerOnofri.CircleHardyDefinitions

@[expose] public section

/-! Haar normalization of a one-sided boundary factor gives an actual unit
vector in the real Hardy coefficient space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint

theorem boundary_parseval {d : ℕ} (f : C(Torus d,ℂ)) :
    HasSum (fun k => ‖UnitAddTorus.mFourierCoeff f k‖^2)
      (∫ x,Complex.normSq (f x) ∂torusMeasure d) := by
  let F := f.toLp 2 (torusMeasure d) ℂ
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff F
  have hc (k : Frequency d) : UnitAddTorus.mFourierCoeff F k=UnitAddTorus.mFourierCoeff f k :=
    UnitAddTorus.mFourierCoeff_toLp f k
  have hi : (∫ x,‖F x‖^2 ∂torusMeasure d)=(∫ x,Complex.normSq (f x) ∂torusMeasure d) := by
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp (p:=2) (μ:=torusMeasure d) (𝕜:=ℂ)] with x hx
    rw [hx,Complex.sq_norm]
  change HasSum (fun k => ‖UnitAddTorus.mFourierCoeff F k‖^2) (∫ x,‖F x‖^2 ∂torusMeasure d) at h
  rw [hi] at h
  simpa only [hc] using h

theorem hardy_unit_vector (f : C(Torus 1,ℂ))
    (hr : ∀ k,conj (UnitAddTorus.mFourierCoeff f k)=UnitAddTorus.mFourierCoeff f k)
    (hn : ∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0)
    (hm : (∫ x,Complex.normSq (f x) ∂torusMeasure 1)=1) :
    ∃ u : CircleHardy.Space, ‖u‖=1 ∧
      ∀ n : ℕ,(u n:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (n:ℤ)) := by
  let c : ℤ → ℂ := fun z => UnitAddTorus.mFourierCoeff f (fun _ => z)
  have hfull := boundary_parseval f
  rw [hm] at hfull
  have hZ : HasSum (fun z : ℤ => ‖c z‖^2) 1 := by
    exact ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr hfull
  have hneg (n : ℕ) : c (-(n+1:ℤ))=0 := hn (fun _ => -(n+1:ℤ)) (by omega)
  have hN : Summable (fun n : ℕ => ‖c (n:ℤ)‖^2) :=
    hZ.summable.comp_injective (fun a b h => by exact_mod_cast h)
  have hsum : (∑' n : ℕ,‖c (n:ℤ)‖^2)=1 := by
    have h := tsum_nat_add_neg_add_one hZ.summable
    simp only [hneg,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),tsum_zero,add_zero,hZ.tsum_eq] at h
    exact h
  have hreal (z : ℤ) : ((c z).re:ℂ)=c z := Complex.conj_eq_iff_re.mp (hr _)
  have hsq (z : ℤ) : ‖c z‖^2=(c z).re^2 := by
    conv_lhs => rw [← hreal z]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hs : Summable (fun n : ℕ => (c (n:ℤ)).re^2) := by simpa only [hsq] using hN
  let u : CircleHardy.Space := ⟨fun n => (c (n:ℤ)).re,by
    apply memℓp_gen
    simpa using hs⟩
  refine ⟨u,?_,fun n => hreal n⟩
  have hu : ‖u‖^2=1 := by
    have h := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) u
    have he : ‖u‖^2=∑' n : ℕ,(c (n:ℤ)).re^2 := by simpa [u] using h
    rw [he]
    simpa only [hsq] using hsum
  nlinarith [norm_nonneg u]

#print axioms boundary_parseval
#print axioms hardy_unit_vector
end BecknerOnofri.HighDim.CircleOuter
