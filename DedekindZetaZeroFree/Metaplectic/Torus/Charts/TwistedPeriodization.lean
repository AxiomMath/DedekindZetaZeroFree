module

public import DedekindZetaZeroFree.Adeles.Quotients.Torus.UniformPeriodizationSupport
public import DedekindZetaZeroFree.Eisenstein.Induction.RationalDiagonalSmoothness

@[expose] public section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport
open KPGlobalTorusBorelTwistCompatibilityBorelInduction
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem chartTerm_contDiffOn (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
    (g : G F ζ hζ)
    (a : KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartTerm F ζ hζ C s f g a) (groupArchDomain F) := by
  obtain ⟨y, hy⟩ := rationalRep_rational F ζ hζ C a
  unfold chartTerm
  rw [hy]
  exact RationalDiagonalSectionSmoothness.rational_eval_contDiffOn F ζ hζ _ J f hf g y

theorem chartTerm_eventually_zero (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (hf : f ∈ InducedLevel F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s) J)
    (g : G F ζ hζ) (K : Set (GroupArch F)) (hK : IsCompact K)
    (hKU : K ⊆ groupArchDomain F) :
    ∃ S : Finset (KPGlobalTorusPeriodizationInverse.PeriodizationIndex F ζ hζ C),
      ∀ z ∈ K, ∀ a ∉ S, chartTerm F ζ hζ C s f g a z = 0 := by
  obtain ⟨S, hS⟩ := UniformFiberLevel.exists_uniform_chart_support F ζ hζ C s J g
  exact ⟨S, fun z _ a ha => hS ⟨f, hf⟩ z a ha⟩

theorem functionsP_chart_tsum (C : ModelData F ζ hζ) (s : ℂ)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (productModel F ζ hζ C) s))
    (g : G F ζ hζ) (z : GroupArch F) :
    ((functionsP F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)).val.val 1
      = ∑' a, chartTerm F ζ hζ C s f g a z := by
  rw [show (functionsP F ζ hζ C s f).val (groupArchChart F ζ hζ z * g)
      = twistedP F ζ hζ C s (f.val (groupArchChart F ζ hζ z * g)) from rfl]
  rw [twistedP_rational_formula F ζ hζ C s (rationalRep F ζ hζ C)
    (rationalRep_rational F ζ hζ C) (f.val (groupArchChart F ζ hζ z * g)) 1]
  simp [chartTerm, mul_one]

end
end DedekindZetaZeroFree.TorusChartTransport
