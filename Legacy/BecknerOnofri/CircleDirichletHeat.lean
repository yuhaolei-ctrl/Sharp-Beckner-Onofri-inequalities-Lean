module

public import Legacy.BecknerOnofri.CircleHeatStrict

@[expose] public section

/-! The actual reflected Dirichlet heat kernel on the interval (0,1/2). -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat

def dirichletHeat (t x y : ℝ) : ℝ := realHeat t (x-y)-realHeat t (x+y)

theorem realHeat_sum_lt_sub {t u v : ℝ} (ht : 0 < t)
    (hu : u ∈ Ioo (0:ℝ) (1/2)) (hv : v ∈ Ioo (0:ℝ) (1/2)) :
    realHeat t (u+v) < realHeat t (u-v) := by
  have ha : |u-v| ≤ 1/2 := abs_le.mpr ⟨by linarith [hu.1,hv.2],by linarith [hu.2,hv.1]⟩
  have ha0 : |u-v| ∈ Icc (0:ℝ) (1/2) := ⟨abs_nonneg _,ha⟩
  by_cases hsum : u+v ≤ 1/2
  · have hs : u+v ∈ Icc (0:ℝ) (1/2) := ⟨by linarith [hu.1,hv.1],hsum⟩
    have hle : |u-v| < u+v := abs_lt.mpr ⟨by linarith [hu.1],by linarith [hv.1]⟩
    simpa only [realHeat_abs ht] using realHeat_strictAnti ht ha0 hs hle
  · have hs : 1-(u+v) ∈ Icc (0:ℝ) (1/2) := ⟨by linarith [hu.2,hv.2],by linarith⟩
    have hle : |u-v| < 1-(u+v) := abs_lt.mpr ⟨by linarith [hv.2],by linarith [hu.2]⟩
    simpa only [realHeat_one_sub ht,realHeat_abs ht] using realHeat_strictAnti ht ha0 hs hle

theorem dirichletHeat_pos {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0:ℝ) (1/2)) (hy : y ∈ Ioo (0:ℝ) (1/2)) : 0 < dirichletHeat t x y :=
  sub_pos.mpr (realHeat_sum_lt_sub ht hx hy)

theorem dirichletHeat_nonneg {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Icc (0:ℝ) (1/2)) (hy : y ∈ Icc (0:ℝ) (1/2)) : 0 ≤ dirichletHeat t x y :=
  sub_nonneg.mpr (realHeat_sum_le_sub ht hx hy)

theorem dirichletHeat_lt_periodic {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletHeat t x y < realHeat t (x-y) := by
  have hh : 0 < realHeat t (x+y) := theta_re_pos ht _
  dsimp [dirichletHeat]
  linarith

theorem dirichletHeat_symmetric {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletHeat t x y = dirichletHeat t y x := by
  unfold dirichletHeat
  rw [show y-x=-(x-y) by ring,realHeat_even ht,add_comm y x]

theorem dirichletHeat_zero_left {t : ℝ} (ht : 0 < t) (y : ℝ) : dirichletHeat t 0 y = 0 := by
  simp only [dirichletHeat,zero_sub,zero_add,realHeat_even ht,sub_self]

theorem dirichletHeat_half_left {t : ℝ} (ht : 0 < t) (y : ℝ) : dirichletHeat t (1/2) y = 0 := by
  have hh := realHeat_one_sub ht ((1/2)+y)
  rw [show 1-((1/2:ℝ)+y)=(1/2)-y by ring] at hh
  exact sub_eq_zero.mpr hh

theorem dirichletHeat_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : ℝ × ℝ => dirichletHeat t p.1 p.2) := by
  have hc : Continuous (realHeat t) := continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_realHeat ht x).continuousAt)
  exact (hc.comp (continuous_fst.sub continuous_snd)).sub (hc.comp (continuous_fst.add continuous_snd))

theorem dirichletHeat_eq_sine_series {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletHeat t x y = 4*∑' n : ℕ,
      Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.sin (2*Real.pi*(n+1:ℝ)*x)*Real.sin (2*Real.pi*(n+1:ℝ)*y) := by
  have hs1 := summable_cosineTerm ht (x-y)
  have hs2 := summable_cosineTerm ht (x+y)
  have he (n : ℕ) : cosineTerm t n (x-y)-cosineTerm t n (x+y) =
      2*(Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.sin (2*Real.pi*(n+1:ℝ)*x)*Real.sin (2*Real.pi*(n+1:ℝ)*y)) := by
    dsimp [cosineTerm]
    rw [show 2*Real.pi*(n+1:ℝ)*(x-y)=2*Real.pi*(n+1:ℝ)*x-2*Real.pi*(n+1:ℝ)*y by ring,
      show 2*Real.pi*(n+1:ℝ)*(x+y)=2*Real.pi*(n+1:ℝ)*x+2*Real.pi*(n+1:ℝ)*y by ring,Real.cos_sub,Real.cos_add]
    ring
  calc
    _ = 2*((∑' n : ℕ, cosineTerm t n (x-y))-(∑' n : ℕ, cosineTerm t n (x+y))) := by
      rw [dirichletHeat,realHeat_eq_cosine_series ht,realHeat_eq_cosine_series ht]
      ring
    _ = 2*∑' n : ℕ, (cosineTerm t n (x-y)-cosineTerm t n (x+y)) := by rw [hs1.tsum_sub hs2]
    _ = _ := by simp_rw [he]; rw [tsum_mul_left]; ring

#print axioms dirichletHeat_pos
#print axioms dirichletHeat_eq_sine_series
end Legacy.BecknerOnofri.CircleHeat
