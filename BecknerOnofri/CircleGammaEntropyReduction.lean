import BecknerOnofri.CircleGammaMinimum

/-! Exact final algebra in the quantitative circle entropy estimate.
The entropy remainder and moment comparison are explicit analytic inputs;
this lemma does not claim those still-unproved circle theorems. -/
noncomputable section
namespace BecknerOnofri.HighDim.CircleScalar

theorem gamma_entropy_reduction (t a b E T : ℝ) (ht : 0≤t) (ht1 : t<1)
    (hI : rate t≤E)
    (hrem : t^2+a^2/2+T+weight 1 t*(a-t^2)^2+weight 2 t*(b-t*a)^2≤E)
    (ha : besselMoment 2 (parameter t)≤a)
    (hb : |b-besselMoment 3 (parameter t)|≤6*(a-besselMoment 2 (parameter t))) :
    2*Spin.binaryCost t+gamma t+(21/1000)*a^2+(27/40)*T≤E := by
  let L : ℝ := 6*besselMoment 2 (parameter t)-besselMoment 3 (parameter t)-(6-t)*a
  have hL : max 0 L≤|b-t*a| := by
    apply max_le (abs_nonneg _)
    have hupper := (abs_le.mp hb).2
    have hlt : L≤t*a-b := by dsimp [L]; linarith
    exact hlt.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  have hsq : (max 0 L)^2≤(b-t*a)^2 := by
    have h := pow_le_pow_left₀ (le_max_left 0 L) hL 2
    simpa only [sq_abs] using h
  have hw := weight_initial_lower 2 ht ht1
  have hw0 : 0≤weight 2 t := by norm_num at hw; linarith
  have hweighted := mul_le_mul_of_nonneg_left hsq hw0
  have hg := (gamma_constrained_minimum t ht ht1).2 ⟨a,ha,rfl⟩
  dsimp only at hg
  unfold cost at hg
  change gamma t≤(13/40)*rate t+(27/40)*t^2-2*Spin.binaryCost t+
    ((633/2000)*a^2+((27/40)*weight 1 t)*(a-t^2)^2+
      ((27/40)*weight 2 t)*(max 0 L)^2) at hg
  linarith

#print axioms gamma_entropy_reduction
end BecknerOnofri.HighDim.CircleScalar
