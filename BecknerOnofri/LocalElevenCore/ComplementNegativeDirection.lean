module

public import BecknerOnofri.LocalElevenCore.ComplementHessian
public import BecknerOnofri.QuadraticResolvent

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory
open scoped Topology
namespace BecknerOnofri.HighDim.LocalEleven.ComplementHessian
open ContinuousGibbs ContinuousFirstShell QuadraticModes RawComplementGap

theorem synthesis_critical {d : ℕ} (k : Frequency d) (hk : k≠0) (z : ℂ) :
    InCriticalSobolev (synthesis k z) := by
  classical
  refine ⟨(synthesis k z).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
  apply summable_of_ne_finset_zero (s := {⟨k,hk⟩,⟨-k,neg_ne_zero.mpr hk⟩})
  intro l hl
  have hl1 : l.val≠k := by
    intro h
    exact hl (Finset.mem_insert.mpr (Or.inl (Subtype.ext h)))
  have hl2 : l.val≠-k := by
    intro h
    exact hl (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h))))
  simp only [potentialTerm,← coefficient_eq_fourierCoeff,coefficient_synthesis,
    if_neg hl1,if_neg hl2,add_zero,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]

theorem exists_complement_positive_energy {d : ℕ} (hd : 0<d) :
    ∃ q : Space d,InCriticalSobolev q ∧ MeanZero q ∧
      ComplementSupported (fourierCoeff q) ∧ 0<normalizedPotentialEnergy q := by
  let i : Fin d := ⟨0,hd⟩
  let k : Frequency d := axisFrequency i+axisFrequency i
  have hk : k≠0 := sum_ne_zero i i
  let q : Space d := synthesis k 1
  have hq := synthesis_critical k hk (1:ℂ)
  have hmem : q∈complement d := synthesis_mem_complement (complement_double i) 1
  have hm : MeanZero q := hmem.1
  have hc : ComplementSupported (fourierCoeff q) := by
    intro l hl
    rw [← coefficient_eq_fourierCoeff]
    exact (mem_complement_fourier_iff q).mp hmem l hl
  have hcoeff : fourierCoeff q k=1 := by
    rw [← coefficient_eq_fourierCoeff]
    simp only [q,coefficient_synthesis,ite_true,if_neg (show k≠-k from sum_ne_neg_sum i i i i),add_zero]
  have he := (raw_normalizedEnergy_hasSum hd q hq).summable.le_tsum k
    (fun l hl => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg _))
  rw [(raw_normalizedEnergy_hasSum hd q hq).tsum_eq,hcoeff,norm_one,one_pow,mul_one] at he
  have hp : 0<frequencyLength k^d := pow_pos (Legacy.TorusEndpoint.frequencyRadius_pos hk) d
  exact ⟨q,hq,hm,hc,hp.trans_le he⟩

theorem exists_negative_direction {d : ℕ} (hd : 11≤d) :
    ∀ᶠ u : Space d in 𝓝 0,∀ μ : ℝ,0<μ → μ≤2 →
      ∃ q : Space d,InCriticalSobolev q ∧ MeanZero q ∧
        secondVariation (μ*spectralThreshold d) u q<0 := by
  obtain ⟨q,hq,hm,hc,he⟩ := exists_complement_positive_energy (by omega : 0<d)
  filter_upwards [secondVariation_complement_uniform hd] with u hu
  intro μ hμ hμ2
  have h := hu μ hμ hμ2 q hq hc
  exact ⟨q,hq,hm,lt_of_le_of_lt h (by nlinarith)⟩

#print axioms exists_negative_direction
end BecknerOnofri.HighDim.LocalEleven.ComplementHessian
