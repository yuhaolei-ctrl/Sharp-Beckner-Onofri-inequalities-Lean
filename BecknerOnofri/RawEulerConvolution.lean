import BecknerOnofri.RawSubspectralLocalUniqueness

/-! The literal physical Green convolution equation on the full H^d domain,
and the local uniqueness neighborhood requested by the manuscript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology
namespace BecknerOnofri.HighDim.RawSubspectralLocalUniqueness
open ContinuousGibbs ContinuousFirstShell

local instance : (AddCircle.haarAddCircle (T := 1)).IsNegInvariant := by
  have he : AddCircle.haarAddCircle (T := 1) = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm
  rw [he]
  infer_instance

lemma green_convolution_congr {d : ℕ} {u v : Torus d → ℝ}
    (he : u =ᵐ[torusMeasure d] v) (x : Torus d) :
    (∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*(normalizedGibbs u (x-y)-1) ∂torusMeasure d) =
      ∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*(normalizedGibbs v (x-y)-1) ∂torusMeasure d := by
  haveI : (torusMeasure d).IsAddLeftInvariant := by unfold torusMeasure; infer_instance
  haveI : (torusMeasure d).IsNegInvariant := by unfold torusMeasure; infer_instance
  apply integral_congr_ae
  have h := (Measure.measurePreserving_sub_left (torusMeasure d) x).quasiMeasurePreserving.ae
    (gibbs_congr_ae he)
  filter_upwards [h] with y hy
  rw [hy]

lemma continuous_physical_green {d : ℕ} (hd : 0 < d) (β : ℝ) (v : Space d) (x : Torus d) :
    ((β/spectralThreshold d) • greenContinuous d (normalized v-1)) x =
      β*(∫ y, Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*
        (normalizedGibbs v (x-y)-1) ∂torusMeasure d) := by
  change (β/spectralThreshold d)*(∫ y, normalizedGreenKernel d y *
    ((normalized v-1) (x-y)) ∂torusMeasure d) = _
  have he (y : Torus d) : normalizedGreenKernel d y*((normalized v-1) (x-y)) =
      spectralThreshold d*(Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*
        (normalizedGibbs v (x-y)-1)) := by
    rw [ContinuousMap.sub_apply,ContinuousMap.one_apply,normalized_apply]
    change (spectralThreshold d*Legacy.TorusEndpoint.GreenKernelReal.realGreen d y)*
      (normalizedGibbs v (x-y)-1) = _
    ring
  simp only [he,integral_const_mul]
  field_simp [(spectralThreshold_pos hd).ne']

lemma stationary_of_convolution {d : ℕ} (hd : 0 < d) (β : ℝ) (u : Torus d → ℝ)
    (hu : InSobolev (d:ℝ) u)
    (he : u =ᵐ[torusMeasure d] fun x => β*(∫ y,
      Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*(normalizedGibbs u (x-y)-1) ∂torusMeasure d)) :
    ∀ k : NonzeroFrequency d, ((frequencyLength k.val^d:ℝ):ℂ)*fourierCoeff u k.val =
      (β/spectralThreshold d:ℝ)*fourierCoeff (normalizedGibbs u) k.val := by
  obtain ⟨v,hvu,_,_⟩ := exists_continuous_representative hd u hu
  have hEq : (v : Torus d → ℝ) =ᵐ[torusMeasure d]
      (fun x => ((β/spectralThreshold d) • greenContinuous d (normalized v-1)) x) := by
    filter_upwards [hvu,he] with x hvx hex
    rw [hvx,hex,continuous_physical_green hd,green_convolution_congr hvu]
  haveI : (torusMeasure d).IsOpenPosMeasure := by unfold torusMeasure; infer_instance
  have hvEq : v = (β/spectralThreshold d) • greenContinuous d (normalized v-1) :=
    ContinuousMap.coe_injective (Measure.eq_of_ae_eq hEq v.continuous
      (((β/spectralThreshold d) • greenContinuous d (normalized v-1))).continuous)
  have hf : ReducedEquation.full d (β/spectralThreshold d) v = 0 := sub_eq_zero.mpr hvEq
  have hstat := ((ReducedEquation.full_zero_iff_stationary hd _ v).mp hf).2
  intro k
  have h := hstat k
  rw [fourierCoeff_congr_ae hvu,fourierCoeff_congr_ae (gibbs_congr_ae hvu)] at h
  exact h

theorem local_unique_convolution {d : ℕ} (hd : 0 < d) {β₀ : ℝ}
    (hβ : 0 < β₀) (hβσ : β₀ < spectralThreshold d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (β : ℝ) (u : Torus d → ℝ),
      |β-β₀| < ε → InSobolev (d:ℝ) u → MeanZero u → sobolevNorm (d:ℝ) u < ε →
      (u =ᵐ[torusMeasure d] fun x => β*(∫ y,
        Legacy.TorusEndpoint.GreenKernelReal.realGreen d y*(normalizedGibbs u (x-y)-1) ∂torusMeasure d)) →
      u =ᵐ[torusMeasure d] (fun _ => 0) := by
  obtain ⟨ε,hε,hlocal⟩ := local_unique hd hβ hβσ
  exact ⟨ε,hε,fun β u hb hu hm hn he => hlocal β u hb hu hm hn (stationary_of_convolution hd β u hu he)⟩

#print axioms local_unique_convolution
end BecknerOnofri.HighDim.RawSubspectralLocalUniqueness
