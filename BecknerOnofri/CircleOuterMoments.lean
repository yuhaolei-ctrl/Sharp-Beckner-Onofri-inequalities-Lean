module

public import BecknerOnofri.CircleOuterParseval

@[expose] public section

/-! Parseval for a modulated boundary factor identifies its actual density
Fourier coefficients with the Hardy autocorrelation moments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ComplexConjugate
namespace BecknerOnofri.HighDim.CircleOuter
open Legacy.TorusEndpoint

theorem boundary_parseval_inner {d : ℕ} (f g : C(Torus d,ℂ)) :
    HasSum (fun k => conj (UnitAddTorus.mFourierCoeff f k)*UnitAddTorus.mFourierCoeff g k)
      (∫ x,conj (f x)*g x ∂torusMeasure d) := by
  let F := f.toLp 2 (torusMeasure d) ℂ
  let G := g.toLp 2 (torusMeasure d) ℂ
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff F G
  have hf (k : Frequency d) : UnitAddTorus.mFourierCoeff F k=UnitAddTorus.mFourierCoeff f k :=
    UnitAddTorus.mFourierCoeff_toLp f k
  have hg (k : Frequency d) : UnitAddTorus.mFourierCoeff G k=UnitAddTorus.mFourierCoeff g k :=
    UnitAddTorus.mFourierCoeff_toLp g k
  have hi : (∫ x,conj (F x)*G x ∂torusMeasure d)=(∫ x,conj (f x)*g x ∂torusMeasure d) := by
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp (p:=2) (μ:=torusMeasure d) (𝕜:=ℂ),
      g.coeFn_toLp (p:=2) (μ:=torusMeasure d) (𝕜:=ℂ)] with x hfx hgx
    rw [hfx,hgx]
  change HasSum (fun k => conj (UnitAddTorus.mFourierCoeff F k)*UnitAddTorus.mFourierCoeff G k)
    (∫ x,conj (F x)*G x ∂torusMeasure d) at h
  rw [hi] at h
  simpa only [hf,hg] using h

theorem shifted_coefficient {d : ℕ} (f : C(Torus d,ℂ)) (n k : Frequency d) :
    UnitAddTorus.mFourierCoeff (fun x => UnitAddTorus.mFourier (-n) x*f x) k=
      UnitAddTorus.mFourierCoeff f (k+n) := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [smul_eq_mul,neg_add,UnitAddTorus.mFourier_add,mul_assoc]

theorem boundary_autocorrelation {d : ℕ} (f : C(Torus d,ℂ)) (n : Frequency d) :
    HasSum (fun k => conj (UnitAddTorus.mFourierCoeff f k)*UnitAddTorus.mFourierCoeff f (k+n))
      (UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) n) := by
  let g : C(Torus d,ℂ) := (UnitAddTorus.mFourier (-n))*f
  have h := boundary_parseval_inner f g
  have hc (k : Frequency d) : UnitAddTorus.mFourierCoeff g k=UnitAddTorus.mFourierCoeff f (k+n) :=
    shifted_coefficient f n k
  have hi : (∫ x,conj (f x)*g x ∂torusMeasure d)=
      UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) n := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change conj (f x)*(UnitAddTorus.mFourier (-n) x*f x)=
      UnitAddTorus.mFourier (-n) x*(Complex.normSq (f x):ℂ)
    rw [← Complex.mul_conj]
    ring
  rw [hi] at h
  simpa only [hc] using h

theorem hardy_moment_eq_density_coefficient (f : C(Torus 1,ℂ)) (u : CircleHardy.Space)
    (hc : ∀ m : ℕ,(u m:ℂ)=UnitAddTorus.mFourierCoeff f (fun _ => (m:ℤ)))
    (hn : ∀ k,k (0:Fin 1)<0 → UnitAddTorus.mFourierCoeff f k=0) (n : ℕ) :
    CircleHardy.moment u n=
      (UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) (fun _ => (n:ℤ))).re := by
  let a : ℤ → ℂ := fun z => UnitAddTorus.mFourierCoeff f (fun _ => z)
  have h := boundary_autocorrelation f (fun _ => (n:ℤ))
  have hZ : HasSum (fun z : ℤ => conj (a z)*a (z+n))
      (UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) (fun _ => (n:ℤ))) :=
    ((Equiv.funUnique (Fin 1) ℤ).symm.hasSum_iff).mpr h
  have hN := hZ.nat_add_neg_add_one
  have hz (m : ℕ) : a (-(m+1:ℤ))=0 := hn (fun _ => -(m+1:ℤ)) (by omega)
  have hterm (m : ℕ) : conj (a (m:ℤ))*a ((m:ℤ)+n)+
      conj (a (-(m+1:ℤ)))*a (-(m+1:ℤ)+n)=((u (m+n)*u m:ℝ):ℂ) := by
    rw [hz,map_zero,zero_mul,add_zero]
    have h1 : a (m:ℤ)=(u m:ℂ) := (hc m).symm
    have h2 : a ((m:ℤ)+n)=(u (m+n):ℂ) := by
      rw [← Nat.cast_add]
      exact (hc (m+n)).symm
    rw [h1,h2,Complex.conj_ofReal,Complex.ofReal_mul,mul_comm]
  have hh : HasSum (fun m : ℕ => ((u (m+n)*u m:ℝ):ℂ))
      (UnitAddTorus.mFourierCoeff (fun x => (Complex.normSq (f x):ℂ)) (fun _ => (n:ℤ))) := by
    simpa only [hterm] using hN
  have hr := (Complex.reCLM.hasSum hh).tsum_eq
  simpa only [CircleHardy.moment,Complex.reCLM_apply,Complex.ofReal_re] using hr

#print axioms hardy_moment_eq_density_coefficient
end BecknerOnofri.HighDim.CircleOuter
