module

public import BecknerOnofri.ElevenMixture
public import Legacy.BecknerOnofri.StrictCountableMixture

@[expose] public section
noncomputable section
open Finset MeasureTheory Legacy.TorusEndpoint Filter
open scoped BigOperators Topology
namespace Legacy.BecknerOnofri.ElevenMixture
open CosineMixtureEnergy CosineMixtureApproximation
def componentDefect  (N : Fin 11 → ℕ) : ℝ :=
  (∑ i, (Legacy.D10.FiniteScalar.harmonic (N i) : ℝ)) -
    (2 * coupling) * componentEnergy N

def gap : ℝ := 1/22000

theorem gap_pos (hd : 0 < 11) : 0 < gap := by
  unfold gap
  positivity

theorem componentDefect_nonneg  
    (N : Fin 11 → ℕ) : 0 ≤ componentDefect N :=
  sub_nonneg.mpr (component_bound  N)

theorem componentDefect_gap  
    (N : Fin 11 → ℕ) (hN : N ≠ 0) : gap ≤ componentDefect N := by
  classical
  have hd0 : 0 < 11 := by omega
  have hdR : (0 : ℝ) < 11 := Nat.cast_pos.mpr hd0
  obtain ⟨i, hi⟩ : ∃ i, N i ≠ 0 := by
    by_contra h
    push Not at h
    exact hN (funext h)
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 11))) =>
    scalar_indicator_bound  (N j))
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hsum
  have hind : (1 / 2000 : ℝ) ≤ ∑ j, if N j = 0 then 0 else (1 / 2000 : ℝ) := by
    simpa [hi] using single_le_sum (f := fun j => if N j = 0 then 0 else (1 / 2000 : ℝ))
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
  have havg := mul_le_mul_of_nonneg_left
    (MixedBinomialComparison.componentEnergy_le_average_diagonal hd0 N)
    (show 0 ≤ 2*coupling from mul_nonneg (by norm_num) coupling_pos.le)
  have hmul := (mul_le_mul_of_nonneg_left havg hdR.le)
  have heq : (11 : ℝ) * ((2 * coupling) *
      ((1 / (11 : ℝ)) * ∑ j, GaussianLattice.binomialEnergy 11 (N j))) =
      (2 * coupling) * ∑ j, GaussianLattice.binomialEnergy 11 (N j) := by
    field_simp
  norm_num only [Nat.cast_ofNat] at hmul
  rw [heq] at hmul
  have hg : gap = (1 / 2000 : ℝ) / (11 : ℝ) := by unfold gap; ring
  rw [hg]
  apply (div_le_iff₀ hdR).mpr
  unfold componentDefect
  nlinarith

theorem latentWeight_self_pos  (N : Fin 11 → ℕ) : 0 < Legacy.D10.latentWeight N N N := by
  unfold Legacy.D10.latentWeight
  apply prod_pos
  intro i hi
  unfold Legacy.D10.hypergeometricWeightReal Legacy.D10.hypergeometricWeight
  have hc : 0 < (N i + N i).choose (N i) := Nat.choose_pos (by omega)
  norm_cast
  simp only [Nat.choose_self, Nat.cast_one, mul_one]
  exact div_pos (by norm_num) (Nat.cast_pos.mpr hc)

theorem mem_latentBox_self  (N : Fin 11 → ℕ) : N ∈ Legacy.D10.latentBox N := by
  simp [Legacy.D10.latentBox]

variable {α : Type*} 

def latentDefect (w : α → ℝ) (N : α → Fin 11 → ℕ) (a b : α) (L : Fin 11 → ℕ) : ℝ :=
  w a * w b * Legacy.D10.latentWeight (N a) (N b) L * componentDefect L

theorem latentDefect_nonneg 
    (w : α → ℝ) (N : α → Fin 11 → ℕ) (a b : α) (L : Fin 11 → ℕ)
    (ha : 0 ≤ w a) (hb : 0 ≤ w b) : 0 ≤ latentDefect w N a b L :=
  mul_nonneg (Legacy.D10.correlated_latent_nonneg w w N N a b L ha hb)
    (componentDefect_nonneg  L)

theorem finite_mixture_gap 
    (s : Finset α) (w : α → ℝ) (N : α → Fin 11 → ℕ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hm : ∑ a ∈ s, w a = 1)
    (hpos : ∀ x, 0 < CosineMixture.mixture s w N x)
    (a : α) (ha : a ∈ s) (hN : N a ≠ 0) :
    coupling * fourierEnergy (CosineMixture.density s w N hw hm) +
      w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap / 2 ≤
        densityEntropy (CosineMixture.density s w N hw hm).value := by
  have hsmall : w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap ≤
      latentDefect w N a a (N a) :=
    mul_le_mul_of_nonneg_left (componentDefect_gap  (N a) hN)
      (Legacy.D10.correlated_latent_nonneg w w N N a a (N a) (hw a ha) (hw a ha))
  have hsum : latentDefect w N a a (N a) ≤
      ∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L := by
    calc
      _ ≤ ∑ L ∈ Legacy.D10.latentBox (N a), latentDefect w N a a L :=
        single_le_sum (fun L _ => latentDefect_nonneg  w N a a L
          (hw a ha) (hw a ha)) (mem_latentBox_self (N a))
      _ ≤ ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N a), latentDefect w N a c L :=
        single_le_sum (fun c hc => sum_nonneg (fun L _ =>
          latentDefect_nonneg  w N a c L (hw a ha) (hw c hc))) ha
      _ ≤ _ := single_le_sum
        (f := fun b => ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L)
        (fun b hb => sum_nonneg (fun c hc => sum_nonneg (fun L _ =>
        latentDefect_nonneg  w N b c L (hw b hb) (hw c hc)))) ha
  have heq : (∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b), latentDefect w N b c L) =
      (∑ b ∈ s, ∑ c ∈ s, ∑ L ∈ Legacy.D10.latentBox (N b),
        w b * w c * Legacy.D10.latentWeight (N b) (N c) L *
          ∑ i, (Legacy.D10.FiniteScalar.harmonic (L i) : ℝ)) -
        (2 * coupling) * fourierEnergy (CosineMixture.density s w N hw hm) := by
    rw [fourierEnergy_eq_latent]
    simp only [latentDefect, componentDefect, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro b hb
    apply sum_congr rfl
    intro c hc
    apply sum_congr rfl
    intro L hL
    ring
  rw [heq] at hsum
  have haxis := (TorusMarginals.axis_entropy_bound (by omega : 0 < 11)
    (CosineMixture.density s w N hw hm) (CosineMixture.mixture_continuous s w N) hpos).2
  rw [CosineMixtureAxis.density_axis_sum_eq] at haxis
  linarith

theorem countable_mixture_gap  
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (a : ℕ) (hN : N a ≠ 0) :
    coupling * fourierEnergy (probabilityDensity w N hw hm hSup) +
      w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap / 2 ≤
        densityEntropy (probabilityDensity w N hw hm hSup).value := by
  let g : ℕ → ℝ := fun m => ((1 - epsilon m) * w a) * ((1 - epsilon m) * w a) *
    Legacy.D10.latentWeight (N a) (N a) (N a) * gap / 2
  have hvalid : ∀ᶠ m in atTop,
      Summable (densitySpectralTerm (approximatingDensity w N hw hm m)) ∧
      coupling * fourierEnergy (approximatingDensity w N hw hm m) + g m ≤
        densityEntropy (approximatingDensity w N hw hm m).value := by
    filter_upwards [eventually_gt_atTop a] with m ham
    refine ⟨CosineMixtureEnergy.spectral_summable _ _ _ _ _, ?_⟩
    have h := finite_mixture_gap  (range (m + 1)) (finiteWeight w m) (finiteIndex N m)
      (fun n _ => finiteWeight_nonneg w hw hm m n) (finiteWeight_mass w m)
      (approximatingDensity_pos w N hw hm m) a (by simp; omega)
      (by simpa [finiteIndex, ham] using hN)
    simpa only [finiteWeight, finiteIndex, if_pos ham, approximatingDensity, g] using h
  have hg : Tendsto g atTop (𝓝 (w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap / 2)) := by
    have h : Tendsto (fun m => (1 - epsilon m) * w a) atTop (𝓝 (w a)) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub epsilon_tendsto).mul_const (w a)
    exact (((h.mul h).mul_const _).mul_const _).div_const _
  exact (StrictMixture.spectral_gap_of_limits coupling_pos
    (approximatingDensity w N hw hm) (probabilityDensity w N hw hm hSup) g hvalid
    (EndpointClosure.fourier_tendsto_of_L1 _ _ (density_L1_tendsto w N hw hm hSup))
    (density_entropy_tendsto w N hw hm hSup) hg).2

theorem countable_mixture_strict_of_component  
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (a : ℕ) (ha : 0 < w a) (hN : N a ≠ 0) :
    coupling * fourierEnergy (probabilityDensity w N hw hm hSup) <
      densityEntropy (probabilityDensity w N hw hm hSup).value := by
  have hgap := countable_mixture_gap  w N hw hm hSup a hN
  have hpositive : 0 < w a * w a * Legacy.D10.latentWeight (N a) (N a) (N a) * gap / 2 :=
    div_pos (mul_pos (mul_pos (mul_pos ha ha) (latentWeight_self_pos (N a)))
      (gap_pos (by omega))) (by norm_num)
  linarith

theorem countable_uniform_of_no_component 
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hn : ∀ n, 0 < w n → N n = 0) (x : Torus 11) : rho w N x = 1 := by
  unfold rho
  have heq : (fun n => w n * CosineMixture.tensor (N n) x) = w := by
    funext n
    by_cases h : w n = 0
    · simp [h]
    · rw [hn n (lt_of_le_of_ne (hw n) (Ne.symm h))]
      simp only [Pi.zero_def, tensor_zero_index, mul_one]
  rw [heq, hm.tsum_eq]

theorem countable_mixture_uniform_of_equality  
    (w : ℕ → ℝ) (N : ℕ → Fin 11 → ℕ) (hw : ∀ n, 0 ≤ w n) (hm : HasSum w 1)
    (hSup : Summable (fun n => w n * CosineMixture.tensor (N n) 0))
    (heq : coupling * fourierEnergy (probabilityDensity w N hw hm hSup) =
      densityEntropy (probabilityDensity w N hw hm hSup).value) : ∀ x, rho w N x = 1 := by
  apply countable_uniform_of_no_component w N hw hm
  intro n hn
  by_contra hN
  exact (ne_of_lt (countable_mixture_strict_of_component  w N hw hm hSup n hn hN)) heq


#print axioms countable_mixture_gap
#print axioms countable_mixture_uniform_of_equality
end Legacy.BecknerOnofri.ElevenMixture
