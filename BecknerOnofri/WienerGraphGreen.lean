import BecknerOnofri.WienerGraphOperator
import BecknerOnofri.LocalElevenCore.InverseGreenWiener

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell ContinuousComplement

lemma green_coefficient_bound {d : ℕ} (hd : 0<d) (u : Space d) (k : Frequency d) :
    ‖coefficient k (greenContinuous d u)‖≤‖coefficient k u‖ := by
  rw [coefficient_green hd]
  by_cases hk : k=0
  · simp [hk]
  · rw [if_neg hk,norm_mul,Complex.norm_real]
    have he := GreenCritical.nonzero_eigenvalue_ge_one (⟨k,hk⟩ : NonzeroFrequency d)
    have hp : 0<frequencyLength k^d := lt_of_lt_of_le zero_lt_one he
    rw [Real.norm_of_nonneg (div_nonneg zero_le_one hp.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hp).mpr he)

def green {d : ℕ} (hd : 0<d) (m : ℕ) : graph d m →L[ℝ] graph d m :=
  liftContraction m (greenContinuous d) (green_coefficient_bound hd)

@[simp] lemma toContinuous_green {d : ℕ} (hd : 0<d) (m : ℕ) (x : graph d m) :
    toContinuous d m (green hd m x)=greenContinuous d (toContinuous d m x) := rfl

def complementProjection (d : ℕ) : Space d →L[ℝ] Space d :=
  (complement d).subtypeL.comp (complementMap d)

lemma complement_coefficient_bound (d : ℕ) (u : Space d) (k : Frequency d) :
    ‖coefficient k (complementProjection d u)‖≤‖coefficient k u‖ := by
  classical
  change ‖coefficient k (complementMap d u).val‖≤_
  rw [BecknerOnofri.HighDim.QuadraticModes.complementMap_coefficient]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (coefficient k u)

def projection (d m : ℕ) : graph d m →L[ℝ] graph d m :=
  liftContraction m (complementProjection d) (complement_coefficient_bound d)

@[simp] lemma toContinuous_projection {d m : ℕ} (x : graph d m) :
    toContinuous d m (projection d m x)=(complementMap d (toContinuous d m x)).val := rfl

def slavingInverse {d : ℕ} (hd : 11≤d) (m : ℕ) : graph d m →L[ℝ] graph d m :=
  liftContraction m ((complement d).subtypeL.comp (LocalEleven.QuadraticSlaving.inverseGreen hd))
    (LocalEleven.QuadraticSlaving.inverseGreen_coefficient_bound hd)

@[simp] lemma toContinuous_slavingInverse {d : ℕ} (hd : 11≤d) (m : ℕ) (x : graph d m) :
    toContinuous d m (slavingInverse hd m x)=
      (LocalEleven.QuadraticSlaving.inverseGreen hd (toContinuous d m x)).val := rfl

#print axioms green_coefficient_bound
#print axioms toContinuous_slavingInverse
end BecknerOnofri.HighDim.WienerGraph
