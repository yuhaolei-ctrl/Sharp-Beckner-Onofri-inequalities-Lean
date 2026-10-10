module

public import BecknerOnofri.AnalyticSquareParameter
public import BecknerOnofri.AnalyticScalarInverse
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order

@[expose] public section

/-! # An analytic cubic remainder in the onset variable

Pure one-variable analysis (no development-specific objects).  Let `E, D` be real analytic germs
at `0`, even in `t`, with `D = κ t² + O(t⁴)` (`κ ≠ 0`) and `E - a D² = O(t⁶)`.  Then in the
variable `δ = D(t)` the energy is `a δ² + δ³ R(δ)` with `R` analytic:
`E t = a D(t)² + D(t)³ R(D(t))` for all small `t`.

This is the shape `P = (d/2κ) δ² + δ³ R(δ)` of display `(5.analytic-pressure-remainder)`, obtained
here without differentiating any big-O estimate. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Asymptotics
open scoped Topology

namespace BecknerOnofri.V2.Reaudit.MorseBott

/-- A germ vanishing at `0` is `t` times an analytic germ. -/
theorem exists_mul_factor {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (h0 : f 0 = 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ ∀ t : ℝ, f t = t * g t := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨dslope f 0, (hp.has_fpower_series_dslope_fslope).analyticAt, fun t => ?_⟩
  have := sub_smul_dslope f 0 t
  rw [smul_eq_mul, sub_zero, h0, sub_zero] at this
  exact this.symm

/-- If `H(t²) = O(t⁶)` for an analytic `H`, then `H(x) = x³ h(x)` with `h` analytic. -/
theorem exists_cube_factor_of_sq_bigO {H : ℝ → ℝ} (hH : AnalyticAt ℝ H 0)
    (h : (fun t : ℝ => H (t ^ 2)) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 6) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ ∀ᶠ x in 𝓝 (0 : ℝ), H x = x ^ 3 * g x := by
  by_cases htop : analyticOrderAt H 0 = ⊤
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [analyticOrderAt_eq_top.mp htop] with x hx
    simp [hx]
  obtain ⟨g, hg, hg0, hHg⟩ := hH.analyticOrderAt_ne_top.mp htop
  set n := analyticOrderNatAt H 0 with hn
  have h3 : 3 ≤ n := by
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨C, hCpos, hC⟩ := h.exists_pos
    have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_pow 2 : Continuous fun t : ℝ => t ^ 2).tendsto (0 : ℝ))
    have hHg' := hsq.eventually hHg
    -- `g(t²) = O(‖t‖^(6-2n))`
    have hbd : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖g (t ^ 2)‖ ≤ C * ‖t‖ ^ (6 - 2 * n) := by
      filter_upwards [hC.bound.filter_mono nhdsWithin_le_nhds,
        hHg'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht he hne
      have ht0 : t ≠ 0 := hne
      have hpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
      rw [he] at ht
      have e1 : ‖(t ^ 2 - 0) ^ n • g (t ^ 2)‖ = |t| ^ (2 * n) * |g (t ^ 2)| := by
        rw [norm_smul, sub_zero, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, pow_mul,
          sq_abs]
      have e2 : ‖(‖t‖ ^ 6 : ℝ)‖ = |t| ^ (2 * n) * |t| ^ (6 - 2 * n) := by
        rw [Real.norm_eq_abs, abs_pow, Real.norm_eq_abs, abs_abs, ← pow_add]
        congr 1; omega
      rw [e1, e2] at ht
      have hpn : 0 < |t| ^ (2 * n) := by
        have : 0 < |t| := abs_pos.mpr ht0
        positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have : |t| ^ (2 * n) * |g (t ^ 2)| ≤ |t| ^ (2 * n) * (C * |t| ^ (6 - 2 * n)) := by
        calc _ ≤ _ := ht
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hpn
    have hlim : Tendsto (fun t : ℝ => g (t ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
      have hexp : 0 < 6 - 2 * n := by omega
      have h0 : Tendsto (fun t : ℝ => C * ‖t‖ ^ (6 - 2 * n)) (𝓝[≠] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => C * ‖t‖ ^ (6 - 2 * n)) (𝓝 0) (𝓝 (C * ‖(0 : ℝ)‖ ^ (6 - 2 * n))) :=
          (continuous_const.mul ((continuous_norm).pow _)).continuousAt.tendsto
        simpa [Nat.pos_iff_ne_zero.mp hexp] using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' hbd h0
    have hcont : Tendsto (fun t : ℝ => g (t ^ 2)) (𝓝[≠] 0) (𝓝 (g 0)) := by
      have := (hg.continuousAt.tendsto.comp hsq)
      exact this.mono_left nhdsWithin_le_nhds
    exact hg0 (tendsto_nhds_unique hcont hlim)
  refine ⟨fun x => x ^ (n - 3) * g x, (analyticAt_id.pow _).mul hg, ?_⟩
  filter_upwards [hHg] with x hx
  rw [hx]
  simp only [sub_zero, smul_eq_mul]
  have : x ^ n = x ^ 3 * x ^ (n - 3) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- **Analytic cubic remainder in the onset variable.** -/
theorem exists_delta_remainder {E D : ℝ → ℝ} {κ a : ℝ} (hκ : κ ≠ 0)
    (hE : AnalyticAt ℝ E 0) (hD : AnalyticAt ℝ D 0)
    (hEe : ∀ᶠ t in 𝓝 (0 : ℝ), E (-t) = E t) (hDe : ∀ᶠ t in 𝓝 (0 : ℝ), D (-t) = D t)
    (hE0 : E 0 = 0) (hD0 : D 0 = 0)
    (hDexp : (fun t => D t - κ * t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 4)
    (hmain : (fun t => E t - a * D t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 6) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧ ∀ᶠ t in 𝓝 (0 : ℝ), E t = a * D t ^ 2 + D t ^ 3 * R (D t) := by
  -- growth of `D` and `E`
  have hsq : (fun t : ℝ => κ * t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 2 := by
    refine IsBigO.of_bound |κ| (Eventually.of_forall fun t => ?_)
    simp [abs_mul, Real.norm_eq_abs]
  have hD2 : D =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 2 := by
    have := (hDexp.trans (BecknerOnofri.norm_pow_bigO_of_le (E := ℝ) (by norm_num : 2 ≤ 4))).add hsq
    refine this.congr_left (fun t => ?_)
    simp
  have hDD : (fun t => D t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 4 :=
    (hD2.mul hD2).congr (fun t => by simp [sq]) (fun t => by ring)
  have hE3 : (fun t => E t - E 0 - 0 * t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 3 := by
    have h1 := hmain.trans (BecknerOnofri.norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3 ≤ 6))
    have h2 := (hDD.const_mul_left a).trans
      (BecknerOnofri.norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3 ≤ 4))
    refine (h1.add h2).congr_left (fun t => ?_)
    simp [hE0]
  have hD3 : (fun t => D t - D 0 - κ * t ^ 2) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 3 := by
    refine (hDexp.trans (BecknerOnofri.norm_pow_bigO_of_le (E := ℝ) (by norm_num : 3 ≤ 4))).congr_left
      (fun t => ?_)
    simp [hD0]
  obtain ⟨F, hF, hF0, hFd, hFeq⟩ := AnalyticEvenSquare.exists_square_parameter hE hEe hE3
  obtain ⟨G, hG, hG0, hGd, hGeq⟩ := AnalyticEvenSquare.exists_square_parameter hD hDe hD3
  have hG0' : G 0 = 0 := hG0.trans hD0
  -- the analytic inverse `ψ` of `G`
  obtain ⟨ψ, hψ, hψ0, hψd, hψl, hψr⟩ := exists_analytic_scalar_inverse hG hG0' hGd hκ
  -- `H = F - a G²` has `H(t²) = O(t⁶)`
  have hH : AnalyticAt ℝ (fun x => F x - a * G x ^ 2) 0 := hF.sub (analyticAt_const.mul (hG.pow 2))
  have hHbig : (fun t : ℝ => (F (t ^ 2) - a * G (t ^ 2) ^ 2)) =O[𝓝 0] fun t : ℝ => ‖t‖ ^ 6 := by
    refine hmain.congr' ?_ (EventuallyEq.rfl)
    filter_upwards [hFeq, hGeq] with t h1 h2
    rw [h1, h2]
  obtain ⟨h, hh, hHeq⟩ := exists_cube_factor_of_sq_bigO hH hHbig
  obtain ⟨ψ₁, hψ₁, hψfac⟩ := exists_mul_factor hψ hψ0
  have hh' : AnalyticAt ℝ h (ψ 0) := by simpa [hψ0] using hh
  refine ⟨fun δ => ψ₁ δ ^ 3 * h (ψ δ), (hψ₁.pow 3).mul (hh'.comp hψ), ?_⟩
  -- `ψ(D t) = t²` for small `t`
  have hDt : Tendsto D (𝓝 0) (𝓝 0) := by simpa [hD0] using hD.continuousAt.tendsto
  have hsqt : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_pow 2 : Continuous fun t : ℝ => t ^ 2).tendsto (0 : ℝ))
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by simpa [hψ0] using hψ.continuousAt.tendsto
  filter_upwards [hFeq, hGeq, hsqt.eventually hψl, hsqt.eventually hHeq,
    hsqt.eventually (hψt.eventually hHeq)] with t h1 h2 h3 h4 h5
  have hx : ψ (D t) = t ^ 2 := by rw [h2]; exact h3
  have hfac := hψfac (D t)
  rw [hx] at hfac
  have h4' : F (t ^ 2) - a * G (t ^ 2) ^ 2 = (t ^ 2) ^ 3 * h (t ^ 2) := h4
  have hEt : E t = F (t ^ 2) := h1
  have hDt' : D t = G (t ^ 2) := h2
  show E t = a * D t ^ 2 + D t ^ 3 * (ψ₁ (D t) ^ 3 * h (ψ (D t)))
  rw [hx, hEt, hDt']
  rw [hDt'] at hfac
  have : G (t ^ 2) ^ 3 * (ψ₁ (G (t ^ 2)) ^ 3 * h (t ^ 2)) = (t ^ 2) ^ 3 * h (t ^ 2) := by
    rw [← mul_assoc, ← mul_pow, ← hfac]
  rw [this, ← h4']
  ring

end BecknerOnofri.V2.Reaudit.MorseBott

#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_mul_factor
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_cube_factor_of_sq_bigO
#print axioms BecknerOnofri.V2.Reaudit.MorseBott.exists_delta_remainder
