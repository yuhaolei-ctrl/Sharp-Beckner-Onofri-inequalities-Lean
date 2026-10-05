module

public import BecknerOnofri.OnsetCompactness

@[expose] public section

/-! Compactness of global optimizers for coefficients converging to any
strictly subcritical value. The limit remains a genuine global optimizer. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BecknerOnofri.SubcriticalOptimizerCompactness
open Legacy.TorusEndpoint Legacy.BecknerOnofri
open TorusSobolev SubcriticalAttainment

lemma eventual_energy_bound {d : ℕ} {b Ab A₀ : ℝ}
    (hR : RoughExponentialBound d b Ab) (hgap : 1/(4*b) < A₀)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 A₀))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, u n ∈ realSobolevBall d B := by
  let a := (1/(4*b)+A₀)/2
  have ha : 1/(4*b) < a := by dsimp [a]; linarith
  have ha' : a < A₀ := by dsimp [a]; linarith
  let B := (Real.log Ab+1)/(a-1/(4*b))
  have hB : 0 ≤ B := div_nonneg (by linarith [rough_log_nonneg hR]) (sub_pos.mpr ha).le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hA.eventually (lt_mem_nhds ha')] with n hn
  have hz : 0 ≤ functional (A n) (u n) := by simpa using hmax n 0 (admissible_zero d)
  have hc := coercivity hR (A n) (hu n)
  refine ⟨⟨(hu n).2, ?_⟩, (hu n).1⟩
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith [energy_nonneg (u n)]

lemma limit_maximizes {d : ℕ} {b Ab B A₀ : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hA₀ : 0 ≤ A₀)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 A₀))
    {u : ℕ → TorusL2 d}
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n))
    (hbound : ∀ᶠ n in atTop, u n ∈ realSobolevBall d B)
    {v : TorusL2 d} (hv : v ∈ realSobolevBall d B)
    (hlim : Tendsto u atTop (𝓝 v)) :
    ∀ w : TorusL2 d, Admissible w → functional A₀ w ≤ functional A₀ v := by
  intro w hw
  have hErr : Tendsto (fun n => |A n-A₀| *(B+criticalEnergy w)) atTop (𝓝 0) := by
    simpa using ((hA.sub (tendsto_const_nhds (x := A₀))).abs.mul_const (B+criticalEnergy w))
  have hlo : ∀ᶠ n in atTop,
      functional A₀ w-|A n-A₀| *(B+criticalEnergy w) ≤ functional A₀ (u n) := by
    filter_upwards [hbound] with n hn
    have hm := hmax n w hw
    have h1 := mul_le_mul_of_nonneg_right (neg_abs_le (A n-A₀)) (energy_nonneg (u n))
    have h2 := mul_le_mul_of_nonneg_left hn.1.2 (abs_nonneg (A n-A₀))
    have h3 := mul_le_mul_of_nonneg_right (le_abs_self (A n-A₀)) (energy_nonneg w)
    unfold functional at hm ⊢
    nlinarith
  by_contra hn
  have hlt : functional A₀ v < functional A₀ w := lt_of_not_ge hn
  let z := (functional A₀ v+functional A₀ w)/2
  have hvz : functional A₀ v < z := by dsimp [z]; linarith
  have hzw : z < functional A₀ w := by dsimp [z]; linarith
  have ht : Tendsto u atTop (𝓝[realSobolevBall d B] v) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hbound⟩
  have hUpper := ht.eventually ((functional_upperSemicontinuousOn_ball hb hA₀ hR) v hv z hvz)
  have hSmall := hErr.eventually (gt_mem_nhds (sub_pos.mpr hzw))
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hlo, hUpper, hSmall] with n h1 h2 h3
    linarith
  exact hfalse.exists.elim (fun _ hn => hn)

theorem exists_subsequence_limit {d : ℕ} (hd : 0 < d) {b Ab A₀ : ℝ}
    (hb : 0 < b) (hR : RoughExponentialBound d b Ab) (hgap : 1/(4*b) < A₀)
    {A : ℕ → ℝ} (hA : Tendsto A atTop (𝓝 A₀))
    (u : ℕ → TorusL2 d) (hu : ∀ n, Admissible (u n))
    (hmax : ∀ n (v : TorusL2 d), Admissible v → functional (A n) v ≤ functional (A n) (u n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ v : TorusL2 d, v ∈ realSobolevBall d B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 v) ∧
        (∀ᶠ n in atTop, u (φ n) ∈ realSobolevBall d B) ∧
        (∀ w : TorusL2 d, Admissible w → functional A₀ w ≤ functional A₀ v) := by
  obtain ⟨B, hB, hbound⟩ := eventual_energy_bound hR hgap hA u hu hmax
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (realSobolevBall_isCompact hd hB).tendsto_subseq' hbound.frequently
  have hA₀ : 0 ≤ A₀ := le_trans (by positivity) hgap.le
  have hsub := hφ.tendsto_atTop.eventually hbound
  refine ⟨B, hB, v, hv, φ, hφ, hlim, hsub, ?_⟩
  exact limit_maximizes hb hR hA₀ (hA.comp hφ.tendsto_atTop)
    (fun n => hmax (φ n)) hsub hv hlim

#print axioms exists_subsequence_limit
end BecknerOnofri.SubcriticalOptimizerCompactness
