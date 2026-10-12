module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.UpperAndLowerBigCellTransitions

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPLiteralPeriod.NonzeroResidue
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem smooth_right_translate (v : Functions F ζ hζ)
    (hv : Smooth F ζ hζ v) (a : G F ζ hζ) :
    Smooth F ζ hζ ((rightAction F ζ hζ) a v) := by
  rcases hv with ⟨hvcont, hvarch, U, hU⟩
  have hleft (g : G F ζ hζ) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => v (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    apply contDiffOn_of_locally_contDiffOn
    intro z₀ hz₀
    obtain ⟨O, q, hO, hzO, hq, hqO, heq⟩ :=
      KPLiteralChamber.literal_group_chart_local_transition F ζ hζ g z₀ hz₀
    refine ⟨O, hO, hzO, ?_⟩
    have hc := (hvarch
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z₀ * g)).comp hq hqO
    exact (hc.congr (fun z hz => congrArg v (heq z hz))).mono
      Set.inter_subset_right
  refine ⟨?_, ?_, ?_⟩
  · change Continuous (fun g => v (g * a))
    exact hvcont.comp (continuous_id.mul continuous_const)
  · intro g
    change ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => v ((g * KPGlobalResidualConstruction.archChart F ζ hζ x) * a))
      (KPGlobalResidualConstruction.archDomain F)
    apply contDiffOn_of_locally_contDiffOn
    intro x₀ hx₀
    obtain ⟨O, q, hO, hxO, hq, hqO, heq⟩ :=
      KPLiteralChamber.literal_right_to_left_chart_local_transition F ζ hζ g x₀ hx₀
    refine ⟨O, hO, hxO, ?_⟩
    have hc := (hleft ((g * KPGlobalResidualConstruction.archChart F ζ hζ x₀) * a)).comp
      hq hqO
    apply (hc.congr (fun x hx => ?_)).mono Set.inter_subset_right
    rw [heq x hx, mul_assoc]
    rfl
  · obtain ⟨V, hV⟩ :=
      KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel.exists_conjugate_finite_level
        F ζ hζ U a
    refine ⟨V, ?_⟩
    intro g u hu
    change v ((g * u) * a) = v (g * a)
    have h := hU (g * a) (a⁻¹ * u * a) (hV ⟨u, hu⟩)
    simpa only [mul_assoc, mul_inv_cancel_left] using h

end DedekindZetaZeroFree.KPLiteralPeriod.NonzeroResidue

end
