module

public import Legacy.BecknerOnofri.SubcriticalFourierVariation

@[expose] public section

/-! Removing the actual mean of a real critical Sobolev potential preserves
its Fourier energy and gives the standard mean-zero admissible class. -/
noncomputable section
open MeasureTheory Legacy.TorusEndpoint
namespace Legacy.BecknerOnofri.SobolevCentering
open TorusSobolev SubcriticalAttainment

def constant (d : ℕ) (c : ℂ) : TorusL2 d := Lp.const 2 (torusMeasure d) c

theorem constant_ae (d : ℕ) (c : ℂ) : constant d c =ᵐ[torusMeasure d] (fun _ => c) := Lp.coeFn_const _ _ _

theorem fourier_zero (d : ℕ) (u : TorusL2 d) :
    fourierIsometry d u 0 = ∫ x, u x ∂torusMeasure d := by
  simp only [fourierIsometry_apply,UnitAddTorus.mFourierCoeff,neg_zero,UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply,one_smul]
  rfl

theorem constant_eq_basis (d : ℕ) (c : ℂ) :
    constant d c = c • (SubcriticalEuler.characterLp (0:Frequency d) : TorusL2 d) := by
  have hb : (SubcriticalEuler.characterLp (0:Frequency d) : TorusL2 d) =ᵐ[torusMeasure d]
      fun x => UnitAddTorus.mFourier (0:Frequency d) x := by
    unfold SubcriticalEuler.characterLp
    rw [UnitAddTorus.coe_mFourierBasis]
    exact ContinuousMap.coeFn_toLp (torusMeasure d) (UnitAddTorus.mFourier (0:Frequency d))
  apply Lp.ext
  filter_upwards [constant_ae d c,Lp.coeFn_smul c (SubcriticalEuler.characterLp (0:Frequency d) : TorusL2 d),hb]
    with x hc hs hb
  rw [hc,hs]
  change c = c * (SubcriticalEuler.characterLp (0:Frequency d) : TorusL2 d) x
  rw [hb]
  simp only [UnitAddTorus.mFourier_zero,ContinuousMap.one_apply,mul_one]

theorem constant_fourier (d : ℕ) (c : ℂ) (k : Frequency d) :
    fourierIsometry d (constant d c) k = if k = 0 then c else 0 := by
  classical
  have hb : fourierIsometry d (SubcriticalEuler.characterLp (0:Frequency d)) = lp.single 2 0 1 :=
    (UnitAddTorus.mFourierBasis (d := Fin d)).repr_self 0
  rw [constant_eq_basis,map_smul,hb,lp.coeFn_smul]
  simp only [Pi.smul_apply,lp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

def center {d : ℕ} (u : TorusL2 d) : TorusL2 d := u-constant d (fourierIsometry d u 0)

theorem center_fourier {d : ℕ} (u : TorusL2 d) (k : Frequency d) :
    fourierIsometry d (center u) k = fourierIsometry d u k - if k=0 then fourierIsometry d u 0 else 0 := by
  rw [center,map_sub,lp.coeFn_sub]
  change fourierIsometry d u k-fourierIsometry d (constant d (fourierIsometry d u 0)) k = _
  rw [constant_fourier]

theorem center_weightedSquare {d : ℕ} (hd : 0 < d) (u : TorusL2 d) (k : Frequency d) :
    weightedSquare (fourierIsometry d (center u)) k = weightedSquare (fourierIsometry d u) k := by
  rw [weightedSquare,center_fourier]
  by_cases hk : k=0
  · simp [hk,frequencyRadius,hd.ne',weightedSquare]
  · simp [hk,weightedSquare]

theorem center_criticalSobolev {d : ℕ} (hd : 0 < d) (u : TorusL2 d)
    (hu : Summable (weightedSquare (fourierIsometry d u))) : CriticalSobolev (center u) := by
  refine ⟨by simp [center_fourier],?_⟩
  exact hu.congr (fun k => (center_weightedSquare hd u k).symm)

theorem center_energy {d : ℕ} (hd : 0 < d) (u : TorusL2 d) : criticalEnergy (center u) = criticalEnergy u := by
  unfold criticalEnergy coefficientEnergy
  exact tsum_congr (center_weightedSquare hd u)

theorem center_ae {d : ℕ} (u : TorusL2 d) :
    center u =ᵐ[torusMeasure d] fun x => u x - (∫ y, u y ∂torusMeasure d) := by
  filter_upwards [Lp.coeFn_sub u (constant d (fourierIsometry d u 0)),constant_ae d (fourierIsometry d u 0)] with x hs hc
  change (u-constant d (fourierIsometry d u 0)) x = _
  rw [hs]
  change u x-constant d (fourierIsometry d u 0) x = _
  rw [hc,fourier_zero]

theorem center_real_ae {d : ℕ} (u : TorusL2 d) :
    (fun x => (center u x).re) =ᵐ[torusMeasure d]
      fun x => (u x).re - (∫ y, (u y).re ∂torusMeasure d) := by
  filter_upwards [center_ae u] with x hx
  have hi : (∫ y, (u y).re ∂torusMeasure d) = (∫ y, u y ∂torusMeasure d).re :=
    integral_re ((Lp.memLp u).integrable (by norm_num))
  rw [hx,Complex.sub_re,hi]

theorem center_real {d : ℕ} {u : TorusL2 d} (hu : RealPotential u) : RealPotential (center u) := by
  have him : (∫ y, u y ∂torusMeasure d).im = 0 := by
    have hi : (∫ y, (u y).im ∂torusMeasure d) = (∫ y, u y ∂torusMeasure d).im :=
      integral_im ((Lp.memLp u).integrable (by norm_num))
    rw [← hi]
    exact integral_eq_zero_of_ae hu
  filter_upwards [center_ae u,hu] with x hx hr
  rw [hx,Complex.sub_im,hr,him,sub_self]

theorem center_admissible {d : ℕ} (hd : 0 < d) {u : TorusL2 d} (hr : RealPotential u)
    (hs : Summable (weightedSquare (fourierIsometry d u))) : Admissible (center u) :=
  ⟨center_real hr,center_criticalSobolev hd u hs⟩

theorem center_zero_iff_constant {d : ℕ} (u : TorusL2 d) :
    center u = 0 ↔ ∃ c : ℂ, u =ᵐ[torusMeasure d] fun _ => c := by
  constructor
  · intro hz
    refine ⟨fourierIsometry d u 0,?_⟩
    have he : u = constant d (fourierIsometry d u 0) := sub_eq_zero.mp hz
    exact (Lp.ext_iff.mp he).trans (constant_ae _ _)
  · rintro ⟨c,hc⟩
    have he : u = constant d c := Lp.ext (hc.trans (constant_ae d c).symm)
    rw [he,center,constant_fourier]
    simp

#print axioms center_admissible
#print axioms center_energy
#print axioms center_zero_iff_constant
end Legacy.BecknerOnofri.SobolevCentering
