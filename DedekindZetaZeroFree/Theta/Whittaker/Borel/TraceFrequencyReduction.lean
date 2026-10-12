module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPWildBorelFrequencyReduction
open KPGlobalTorusFunctionData

open _root_.DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod renaming global_root_continuous → KPWildIndependentGenericity.NonzeroPeriod.global_root_continuous
open _root_.DedekindZetaZeroFree.KPWildIndependentGenericity.NonzeroPeriod renaming globalRoot_rationalDiagonal_conjugation → KPWildIndependentGenericity.NonzeroPeriod.globalRoot_rationalDiagonal_conjugation
open _root_.DedekindZetaZeroFree.KPCompactFourier renaming char_integral_zero → KPCompactFourier.char_integral_zero

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem rational_root_invariant
    (θ : G F ζ hζ → ℂ)
    (hθ : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g)
    (t : F) (g : G F ζ hζ) :
    θ (N F ζ hζ (algebraMap F (Adeles F) t) * g) = θ g := by
  have he : N F ζ hζ (algebraMap F (Adeles F) t) =
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLQuotient F (KubotaRankTwo.n F t)) := by
    change KPRationalAdelicSplitting.pglN F ζ hζ _ = _
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    unfold KPRationalAdelicSplitting.pglN
    rw [KPRationalAdelicSplitting.N_rational]
  rw [he]
  exact hθ _ g

theorem borel_nontrivial_fourier_zero_iff_standard_trace_zero
    (μ : Measure (KPCompactFourier.AdditiveQuotient F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (θ : G F ζ hζ → ℂ) (hθcont : Continuous θ)
    (hθrat : ∀ γ g, θ (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ γ * g) = θ g) :
    (∀ (b : borel F ζ hζ) (χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle),
      Continuous χ → χ ≠ 1 →
        (∫ x, θ (N F ζ hζ (KPCompactFourier.representative F x) * b.val) *
          (χ x : ℂ) ∂μ) = 0) ↔
    (∀ b : borel F ζ hζ,
      (∫ x, θ (N F ζ hζ (KPCompactFourier.representative F x) * b.val) *
        (adelicTraceQuotientCharacter F x : ℂ) ∂μ) = 0) := by
  constructor
  · intro h b
    exact h b (adelicTraceQuotientCharacter F)
      (continuous_adelicTraceQuotientCharacter F) (adelicTraceQuotientCharacter_ne_one F)
  · intro hp
    let : IsTopologicalGroup (G F ζ hζ) :=
      (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
    let n : AddChar (Adeles F) (borel F ζ hζ) :=
      { toFun := fun x => ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x)
        map_zero_eq_one' := (ActualBorelRetraction.rootInBorel F ζ hζ).map_one
        map_add_eq_mul' := (ActualBorelRetraction.rootInBorel F ζ hζ).map_mul }
    let a : Fˣ → borel F ζ hζ := fun t =>
      ActualBorelRetraction.torusInBorel F ζ hζ
        ⟨rationalDiagonalLift F ζ hζ t, rationalDiagonalLift_mem F ζ hζ t⟩
    let θB : borel F ζ hζ → ℂ := fun b => θ b.val
    have hncont : Continuous n :=
      (KPWildIndependentGenericity.NonzeroPeriod.global_root_continuous F ζ hζ).subtype_mk _
    have hconj (t : Fˣ) (x : Adeles F) :
        n x * a t = a t * n (algebraMap F (Adeles F) (↑t⁻¹ : F) * x) := by
      apply Subtype.ext
      exact KPWildIndependentGenericity.NonzeroPeriod.globalRoot_rationalDiagonal_conjugation
        F ζ hζ t x
    have hθn (t : F) (b : borel F ζ hζ) :
        θB (n (algebraMap F (Adeles F) t) * b) = θB b :=
      rational_root_invariant F ζ hζ θ hθrat t b.val
    have hθa (t : Fˣ) (b : borel F ζ hζ) : θB (a t * b) = θB b := by
      change θ (rationalDiagonalLift F ζ hζ t * b.val) = θ b.val
      exact hθrat (KPRationalAdelicSplitting.rationalPGLQuotient F (rationalDiagonal F t)) b.val
    have hperiod (b : borel F ζ hζ) :
        KPCompactFourier.fourierPeriod F μ (adelicTraceCharacter F) n θB b = 0 := by
      convert hp b using 1
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      have he := adelicTraceQuotientCharacter_mk F (KPCompactFourier.representative F x)
      have hx : (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
          (KPCompactFourier.representative F x) = x := Quotient.out_eq' x
      rw [hx] at he
      exact congrArg (fun z : Circle => (z : ℂ)) he.symm
    have hconst := kp_right_translate_periods_force_constant F μ (adelicTraceCharacter F)
      (continuous_adelicTraceCharacter F) (adelicTraceCharacter_ne_one F)
      (adelicTraceCharacter_diagonal F) n hncont a hconj θB
      (hθcont.comp continuous_subtype_val) hθn hθa hperiod
    intro b χ _hχ hχne
    have hf (x : KPCompactFourier.AdditiveQuotient F) :
        θ (N F ζ hζ (KPCompactFourier.representative F x) * b.val) =
        ∫ y, θ (N F ζ hζ (KPCompactFourier.representative F y) * b.val) ∂μ :=
      hconst b x
    calc
      _ = ∫ x, (∫ y, θ (N F ζ hζ (KPCompactFourier.representative F y) * b.val) ∂μ) *
          (χ x : ℂ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => congrArg (fun c : ℂ => c * (χ x : ℂ)) (hf x))
      _ = 0 := by
        rw [integral_const_mul, KPCompactFourier.char_integral_zero μ χ hχne, mul_zero]

end DedekindZetaZeroFree.KPWildBorelFrequencyReduction

end
