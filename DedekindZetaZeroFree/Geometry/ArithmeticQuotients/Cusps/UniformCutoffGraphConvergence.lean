module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CutoffGraphConvergence

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))
  (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem highEnds_subset_closedHighEnds (T : ℝ) :
    highEnds F ζ hζ hF U a T ⊆ closedHighEnds F ζ hζ hF U a T := by
  intro x hx
  simp only [highEnds, closedHighEnds, Set.mem_iUnion, Set.mem_image] at hx ⊢
  rcases hx with ⟨i,c,y,hy,hxy⟩
  refine ⟨i,c,y,?_,hxy⟩
  rcases hy with ⟨z,hz,rfl⟩
  rcases hz with ⟨w,hw,rfl⟩
  refine ⟨_,⟨w,?_,rfl⟩,rfl⟩
  change T ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w
  exact le_of_lt (show T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w from hw)

 theorem cutoff_next_eventually_one (r : Cutoffs F ζ hζ hF U a)
    (n : ℕ) (hn : r.height_bound ≤ n) (i : Fin a.componentCount) (x : Arch F)
    (hx : basePoint F ζ hζ hF U a i x ∉ highEnds F ζ hζ hF U a n) :
    (fun y : Arch F => r.rho (n+1) (basePoint F ζ hζ hF U a i y)) =ᶠ[nhds x] fun _ => 1 := by
  have hrx := r.on_sublevel n hn _ hx
  have hpos : ∀ᶠ y : Arch F in nhds x, 0 < r.rho n (basePoint F ζ hζ hF U a i y) :=
    (r.smooth n i).continuous.continuousAt.eventually (lt_mem_nhds (by simpa [hrx] : (0:ℝ) < r.rho n (basePoint F ζ hζ hF U a i x)))
  filter_upwards [hpos] with y hy
  apply r.on_sublevel (n+1) (by omega)
  intro hhigh
  have hclosed := highEnds_subset_closedHighEnds F ζ hζ hF U a (↑(n+1)) hhigh
  have hz := r.above_next n hn _ (by simpa only [Nat.cast_add, Nat.cast_one] using hclosed)
  linarith

 theorem laplacian_congr_nhds (d : ℕ) {f g : HyperbolicChart.Space d → ℂ}
    {x : HyperbolicChart.Space d} (h : f =ᶠ[nhds x] g) :
    HyperbolicChart.laplacian d f x = HyperbolicChart.laplacian d g x := by
  have hd (i : Fin d) (k : Fin 3) :
      HyperbolicChart.coordinateDerivative d i k f =ᶠ[nhds x]
        HyperbolicChart.coordinateDerivative d i k g := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : HyperbolicChart.Space d →L[ℝ] ℂ =>
      A (HyperbolicChart.coordinateVector d i k)) hy
  unfold HyperbolicChart.laplacian
  apply Finset.sum_congr rfl
  intro i hi
  have h2 (k : Fin 3) := (hd i k).fderiv_eq (𝕜 := ℝ)
  simp only [HyperbolicChart.coordinateDerivative, h2, h.fderiv_eq (𝕜 := ℝ)]

theorem norm_toLp_le_tail {X E W : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup W]
    {μ : Measure X} {f : X → E} {g : X → W}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : Set X)
    {C : ℝ} (hC : 0 ≤ C) (hoff : ∀ x ∉ t, f x = 0)
    (hbound : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    ‖hf.toLp f‖ ≤ C * (eLpNorm g 2 (μ.restrict t)).toReal := by
  rw [Lp.norm_toLp, ← eLpNorm_restrict_eq_of_support_subset hf.aestronglyMeasurable]
  · have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (hf.restrict t).aestronglyMeasurable (ae_of_all _ hbound) 2
    have hfin : ENNReal.ofReal C * eLpNorm g 2 (μ.restrict t) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hg.restrict t).eLpNorm_ne_top
    have hr := ENNReal.toReal_mono hfin h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hr
  · intro x hx
    by_contra hxt
    exact hx (hoff x hxt)

theorem norm_toLp_le_tail_three {X E W₁ W₂ W₃ : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup W₁]
    [NormedAddCommGroup W₂] [NormedAddCommGroup W₃]
    {μ : Measure X} {f : X → E} {g₁ : X → W₁} {g₂ : X → W₂} {g₃ : X → W₃}
    (hf : MemLp f 2 μ) (h₁ : MemLp g₁ 2 μ) (h₂ : MemLp g₂ 2 μ)
    (h₃ : MemLp g₃ 2 μ) (t : Set X)
    {C : ℝ} (hC : 0 ≤ C) (hoff : ∀ x ∉ t, f x = 0)
    (hbound : ∀ x, ‖f x‖ ≤ C * (‖g₁ x‖ + ‖g₂ x‖ + ‖g₃ x‖)) :
    ‖hf.toLp f‖ ≤ C * ((eLpNorm g₁ 2 (μ.restrict t)).toReal +
      (eLpNorm g₂ 2 (μ.restrict t)).toReal + (eLpNorm g₃ 2 (μ.restrict t)).toReal) := by
  have hsum : MemLp (fun x => ‖g₁ x‖ + ‖g₂ x‖ + ‖g₃ x‖) 2 μ :=
    (h₁.norm.add h₂.norm).add h₃.norm
  have hh := norm_toLp_le_tail hf hsum t hC hoff (by
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖g₁ x‖ + ‖g₂ x‖ + ‖g₃ x‖)] using hbound x)
  have h12 := lpNorm_add_le ((h₁.restrict t).norm) (g := fun x => ‖g₂ x‖) (by norm_num : (1 : ENNReal) ≤ 2)
  have h123 := lpNorm_add_le (((h₁.restrict t).norm).add (h₂.restrict t).norm)
    (g := fun x => ‖g₃ x‖) (by norm_num : (1 : ENNReal) ≤ 2)
  simp only [lpNorm, Pi.add_apply] at h12 h123
  rw [eLpNorm_norm g₁ (h₁.restrict t).aestronglyMeasurable,
    eLpNorm_norm g₂ (h₂.restrict t).aestronglyMeasurable] at h12
  rw [eLpNorm_norm g₃ (h₃.restrict t).aestronglyMeasurable] at h123
  have hs : (eLpNorm (fun x => ‖g₁ x‖ + ‖g₂ x‖ + ‖g₃ x‖) 2 (μ.restrict t)).toReal ≤
      (eLpNorm g₁ 2 (μ.restrict t)).toReal + (eLpNorm g₂ 2 (μ.restrict t)).toReal +
        (eLpNorm g₃ 2 (μ.restrict t)).toReal :=
    h123.trans (add_le_add h12 (le_refl _))
  exact hh.trans (mul_le_mul_of_nonneg_left hs hC)

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
