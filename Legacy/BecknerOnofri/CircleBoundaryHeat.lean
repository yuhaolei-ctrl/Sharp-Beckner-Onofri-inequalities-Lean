module

public import Legacy.BecknerOnofri.CircleDirichletHeat

@[expose] public section

/-! Genuine reflected Neumann and Dirichlet heat kernels, with their strict ordering. -/
noncomputable section
open Set MeasureTheory Legacy.TorusEndpoint TorusHeatPositivity
open scoped BigOperators
namespace Legacy.BecknerOnofri.CircleHeat

def neumannHeat (t x y : ℝ) : ℝ := realHeat t (x-y)+realHeat t (x+y)

theorem neumannHeat_pos {t : ℝ} (ht : 0 < t) (x y : ℝ) : 0 < neumannHeat t x y :=
  add_pos (theta_re_pos ht _) (theta_re_pos ht _)

theorem neumann_sub_dirichlet (t x y : ℝ) :
    neumannHeat t x y-dirichletHeat t x y = 2*realHeat t (x+y) := by
  dsimp [neumannHeat,dirichletHeat]
  ring

theorem dirichletHeat_lt_neumann {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletHeat t x y < neumannHeat t x y := by
  have hp : 0 < realHeat t (x+y) := theta_re_pos ht _
  have hh := neumann_sub_dirichlet t x y
  linarith

theorem neumannHeat_symmetric {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    neumannHeat t x y = neumannHeat t y x := by
  unfold neumannHeat
  rw [show y-x=-(x-y) by ring,realHeat_even ht,add_comm y x]

theorem neumannHeat_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : ℝ × ℝ => neumannHeat t p.1 p.2) := by
  have hc : Continuous (realHeat t) := continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_realHeat ht x).continuousAt)
  exact (hc.comp (continuous_fst.sub continuous_snd)).add (hc.comp (continuous_fst.add continuous_snd))

theorem neumannHeat_eq_cosine_series {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    neumannHeat t x y = 2+4*∑' n : ℕ,
      Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.cos (2*Real.pi*(n+1:ℝ)*x)*Real.cos (2*Real.pi*(n+1:ℝ)*y) := by
  have hs1 := summable_cosineTerm ht (x-y)
  have hs2 := summable_cosineTerm ht (x+y)
  have he (n : ℕ) : cosineTerm t n (x-y)+cosineTerm t n (x+y) =
      2*(Real.exp (-Real.pi*t*(n+1:ℝ)^2)*Real.cos (2*Real.pi*(n+1:ℝ)*x)*Real.cos (2*Real.pi*(n+1:ℝ)*y)) := by
    dsimp [cosineTerm]
    rw [show 2*Real.pi*(n+1:ℝ)*(x-y)=2*Real.pi*(n+1:ℝ)*x-2*Real.pi*(n+1:ℝ)*y by ring,
      show 2*Real.pi*(n+1:ℝ)*(x+y)=2*Real.pi*(n+1:ℝ)*x+2*Real.pi*(n+1:ℝ)*y by ring,Real.cos_sub,Real.cos_add]
    ring
  calc
    _ = 2+2*((∑' n : ℕ, cosineTerm t n (x-y))+(∑' n : ℕ, cosineTerm t n (x+y))) := by
      rw [neumannHeat,realHeat_eq_cosine_series ht,realHeat_eq_cosine_series ht]
      ring
    _ = 2+2*∑' n : ℕ, (cosineTerm t n (x-y)+cosineTerm t n (x+y)) := by rw [hs1.tsum_add hs2]
    _ = _ := by simp_rw [he]; rw [tsum_mul_left]; ring

/-- The length-2π periodic heat kernel, with generator the usual second derivative. -/
def periodicPiHeat (t x : ℝ) : ℝ := (1/(2*Real.pi))*realHeat (t/Real.pi) (x/(2*Real.pi))

def dirichletPiHeat (t x y : ℝ) : ℝ :=
  (1/(2*Real.pi))*dirichletHeat (t/Real.pi) (x/(2*Real.pi)) (y/(2*Real.pi))

def neumannPiHeat (t x y : ℝ) : ℝ :=
  (1/(2*Real.pi))*neumannHeat (t/Real.pi) (x/(2*Real.pi)) (y/(2*Real.pi))

theorem dirichletPiHeat_eq_reflection (t x y : ℝ) :
    dirichletPiHeat t x y = periodicPiHeat t (x-y)-periodicPiHeat t (x+y) := by
  simp only [dirichletPiHeat,periodicPiHeat,dirichletHeat,sub_div,add_div]
  ring

theorem neumannPiHeat_eq_reflection (t x y : ℝ) :
    neumannPiHeat t x y = periodicPiHeat t (x-y)+periodicPiHeat t (x+y) := by
  simp only [neumannPiHeat,periodicPiHeat,neumannHeat,sub_div,add_div]
  ring

theorem div_two_pi_mem {x : ℝ} (hx : x ∈ Ioo (0:ℝ) Real.pi) :
    x/(2*Real.pi) ∈ Ioo (0:ℝ) (1/2) := by
  refine ⟨div_pos hx.1 (by positivity), ?_⟩
  apply (div_lt_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
  linarith [hx.2]

theorem dirichletPiHeat_pos {t x y : ℝ} (ht : 0 < t)
    (hx : x ∈ Ioo (0:ℝ) Real.pi) (hy : y ∈ Ioo (0:ℝ) Real.pi) : 0 < dirichletPiHeat t x y :=
  mul_pos (by positivity) (dirichletHeat_pos (div_pos ht Real.pi_pos) (div_two_pi_mem hx) (div_two_pi_mem hy))

theorem neumannPiHeat_pos {t : ℝ} (ht : 0 < t) (x y : ℝ) : 0 < neumannPiHeat t x y :=
  mul_pos (by positivity) (neumannHeat_pos (div_pos ht Real.pi_pos) _ _)

theorem dirichletPiHeat_lt_neumann {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletPiHeat t x y < neumannPiHeat t x y :=
  mul_lt_mul_of_pos_left (dirichletHeat_lt_neumann (div_pos ht Real.pi_pos) _ _) (by positivity)

theorem dirichletPiHeat_eq_sine_series {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    dirichletPiHeat t x y = (2/Real.pi)*∑' n : ℕ,
      Real.exp (-t*(n+1:ℝ)^2)*Real.sin ((n+1:ℝ)*x)*Real.sin ((n+1:ℝ)*y) := by
  rw [dirichletPiHeat,dirichletHeat_eq_sine_series (div_pos ht Real.pi_pos)]
  have he (n : ℕ) : -Real.pi*(t/Real.pi)*(n+1:ℝ)^2 = -t*(n+1:ℝ)^2 := by field_simp
  have hx (n : ℕ) : 2*Real.pi*(n+1:ℝ)*(x/(2*Real.pi)) = (n+1:ℝ)*x := by field_simp
  have hy (n : ℕ) : 2*Real.pi*(n+1:ℝ)*(y/(2*Real.pi)) = (n+1:ℝ)*y := by field_simp
  simp_rw [he,hx,hy]
  ring

theorem neumannPiHeat_eq_cosine_series {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    neumannPiHeat t x y = 1/Real.pi+(2/Real.pi)*∑' n : ℕ,
      Real.exp (-t*(n+1:ℝ)^2)*Real.cos ((n+1:ℝ)*x)*Real.cos ((n+1:ℝ)*y) := by
  rw [neumannPiHeat,neumannHeat_eq_cosine_series (div_pos ht Real.pi_pos)]
  have he (n : ℕ) : -Real.pi*(t/Real.pi)*(n+1:ℝ)^2 = -t*(n+1:ℝ)^2 := by field_simp
  have hx (n : ℕ) : 2*Real.pi*(n+1:ℝ)*(x/(2*Real.pi)) = (n+1:ℝ)*x := by field_simp
  have hy (n : ℕ) : 2*Real.pi*(n+1:ℝ)*(y/(2*Real.pi)) = (n+1:ℝ)*y := by field_simp
  simp_rw [he,hx,hy]
  ring

#print axioms dirichletPiHeat_pos
#print axioms dirichletPiHeat_lt_neumann
#print axioms dirichletPiHeat_eq_sine_series
end Legacy.BecknerOnofri.CircleHeat
