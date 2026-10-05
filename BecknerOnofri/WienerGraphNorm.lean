module

public import BecknerOnofri.WienerGraphSpace
public import BecknerOnofri.OnsetContinuous

@[expose] public section

noncomputable section
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace BecknerOnofri.HighDim.WienerGraph
open ContinuousGibbs ContinuousFirstShell
open Legacy.BecknerOnofri.RadialWiener Legacy.BecknerOnofri.WeightedWiener
open LocalEleven.GraphRegularity LocalEleven.GraphWienerBounds OnsetWienerBounds

lemma coefficient_norm {d m : ℕ} (x : graph d m) (k : Frequency d) :
    ‖x.val.2 k‖=radialWeight m k*‖coefficient k x.val.1‖ := by
  rw [x.property k,norm_smul,Real.norm_of_nonneg ((radialWeight_isWeight m).nonneg k)]

lemma toContinuous_radial {d m : ℕ} (x : graph d m) : Radial m (toContinuous d m x) := by
  have h := (lp.memℓp x.val.2).summable (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_one,Real.rpow_one,coefficient_norm,Radial,RadialSummable,toContinuous_apply] using h

lemma weighted_memLp {d m : ℕ} (u : Space d) (hu : Radial m u) :
    Memℓp (fun k => radialWeight m k • coefficient k u) 1 := by
  apply (memℓp_gen_iff (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_one,Real.rpow_one,norm_smul,
    Real.norm_of_nonneg ((radialWeight_isWeight m).nonneg _),Radial,RadialSummable] using hu

def ofRadial {d m : ℕ} (u : Space d) (hu : Radial m u) : graph d m :=
  ⟨(u,⟨fun k => radialWeight m k • coefficient k u,weighted_memLp u hu⟩),fun _ => rfl⟩

@[simp] lemma toContinuous_ofRadial {d m : ℕ} (u : Space d) (hu : Radial m u) :
    toContinuous d m (ofRadial u hu)=u := rfl

lemma coefficientSpace_norm {d m : ℕ} (x : graph d m) :
    ‖x.val.2‖=wienerSize m (toContinuous d m x) := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0:ℝ)<(1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,Real.rpow_one,one_div_one,coefficient_norm]
  rfl

lemma continuous_norm_le {d m : ℕ} (u : Space d) (hu : Radial m u) :
    ‖u‖≤wienerSize m u := by
  have h0 := summable_norm (radialWeight_isWeight m) hu
  exact (OnsetContinuous.norm_le_wiener u h0).trans (wienerSize_mono (Nat.zero_le m) u hu)

/-- The complete graph norm is exactly the actual weighted Fourier l1 norm. -/
theorem norm_eq_wienerSize {d m : ℕ} (x : graph d m) :
    ‖x‖=wienerSize m (toContinuous d m x) := by
  change max ‖x.val.1‖ ‖x.val.2‖=_
  rw [coefficientSpace_norm]
  exact max_eq_right (continuous_norm_le _ (toContinuous_radial x))

#print axioms norm_eq_wienerSize
end BecknerOnofri.HighDim.WienerGraph
