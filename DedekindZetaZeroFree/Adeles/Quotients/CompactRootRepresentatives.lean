module

public import DedekindZetaZeroFree.Eisenstein.Induction.RationalBorelCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem compact_root_evaluation_representatives :
    ∃ C : Set (G F ζ hζ), IsCompact C ∧
      ∀ x : KPAdditiveQuotient F, ∃ y ∈ C,
        ∀ f : Functions F ζ hζ,
          (∀ γ a, f (rationalLift F ζ hζ γ * a) = f a) →
          f (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x)) = f y := by
  classical

  obtain ⟨B, hB, hcover⟩ := KPAdelicQuotient.exists_compact_infinite_cover F
  let S : Set (KPAdeles F) :=
    B ×ˢ (KPAdelicTopology.integralAdeles F : Set (KPAdelicTopology.FiniteAdeles F))
  have hS : IsCompact S := hB.prod (KPAdelicTopology.integralAdeles_isCompact F)
  have hcont : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) :=
    KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ
  refine ⟨KPGlobalTorusFunctionData.N F ζ hζ '' S, hS.image hcont, ?_⟩
  intro x

  have hx : QuotientAddGroup.mk' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F)
        (Quotient.out x : KPAdeles F) ∈
      QuotientAddGroup.mk' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) '' S := by
    rw [show QuotientAddGroup.mk' (NumberField.AdeleRing.principalSubgroup (𝓞 F) F) '' S =
        KPAdelicQuotient.quotientMap F '' S from rfl, hcover]
    exact Set.mem_univ _
  obtain ⟨p, hpS, hpeq⟩ := hx
  have hpq : (p : KPAdditiveQuotient F) =
      ((Quotient.out x : KPAdeles F) : KPAdditiveQuotient F) := by
    simpa only [QuotientAddGroup.mk'_apply] using hpeq
  have hsub : p - (Quotient.out x : KPAdeles F) ∈
      NumberField.AdeleRing.principalSubgroup (𝓞 F) F :=
    QuotientAddGroup.eq_iff_sub_mem.mp hpq
  obtain ⟨t, ht⟩ := hsub

  have hout : (Quotient.out x : KPAdeles F) = p + algebraMap F (KPAdeles F) (-t) := by
    rw [map_neg, ht]; abel
  refine ⟨KPGlobalTorusFunctionData.N F ζ hζ p, ⟨p, hpS, rfl⟩, ?_⟩
  intro f hf
  have hN : KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out x : KPAdeles F) =
      KPGlobalTorusFunctionData.N F ζ hζ p *
        rationalLift F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F (-t)) := by
    rw [hout, KPGlobalTorusFunctionData.N_add, KPLiteralExceptionalResidue.rationalLift_unipotent]
  have hcomm : KPGlobalTorusFunctionData.N F ζ hζ p *
        rationalLift F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F (-t)) =
      rationalLift F ζ hζ (KPChamberBruhatTwoCells.rationalUnipotent F (-t)) *
        KPGlobalTorusFunctionData.N F ζ hζ p := by
    rw [KPLiteralExceptionalResidue.rationalLift_unipotent, ← KPGlobalTorusFunctionData.N_add,
      ← KPGlobalTorusFunctionData.N_add, add_comm]
  rw [hN, hcomm]
  exact hf _ _

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity

end
