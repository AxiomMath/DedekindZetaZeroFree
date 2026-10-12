module

public import DedekindZetaZeroFree.Adeles.Characters.RayCharacterCorrectionFactors
public import DedekindZetaZeroFree.Arithmetic.Kummer.HilbertLagrangianProperties
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.SexticHilbertReciprocity
public import DedekindZetaZeroFree.Adeles.Quotients.NormOneSixthUnitCompactness

@[expose] public section

open scoped NumberField Classical nonZeroDivisors
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

noncomputable section
set_option autoImplicit false

namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

def unitQuotientClass (A : SArithmeticData F) : A.UnitQuotient →* A.V :=
  QuotientGroup.lift A.unitSixthPowers (A.sClass.comp A.U.subtype) (by
    intro u hu
    obtain ⟨t, rfl⟩ := hu
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨A.diagonal t.val, by simp [sClass]⟩)

structure GeneralArithmeticContext (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces) where
  principal : IsPrincipalIdealRing A.R
  classGroup_trivial : Subsingleton (ClassGroup A.R)
  fractional_principal : ∀ I : FractionalIdeal A.R⁰ F, IsUnit I →
    ∃ x : Fˣ, I = FractionalIdeal.spanSingleton A.R⁰ (x : F)
  unit_injective : Function.Injective A.unitQuotientClass
  unit_image : A.unitQuotientClass.range = A.E
  correction : A.GaussCorrectionOutput σ η hS
  units_lagrangian : A.IsSelfOrthogonal correction.H A.E
  primary_two : A.PrimaryLagrangianComplementSpec correction.H correction.B 2
  primary_three : A.PrimaryLagrangianComplementSpec correction.H correction.B 3

  reciprocity : A.SexticReciprocitySpec correction.B correction.H

  allowed_integral : ∀ I : A.Exterior, ∃ (r : A.R) (a : Fˣ),
    A.Generates I r ∧ (a : F) = (r : F) ∧ A.IsAllowed correction.B a

  allowed_unique : ∀ (I : FractionalIdeal A.R⁰ F) (a b : Fˣ),
    A.IsAllowedGenerator correction.B I a →
    A.IsAllowedGenerator correction.B I b → a / b ∈ A.sUnitSixthPowers
  normOne_compact : CompactSpace (A.G1 ⧸ A.Gamma1)

  prime_target : ∀ (I : A.Exterior) (v : HeightOneSpectrum (𝓞 F))
    (hIv : I.val = v.asIdeal) (p : A.R) (hp : A.Generates I p)
    (a : Fˣ) (ha : A.IsAllowed correction.B a) (hap : (a : F) = (p : F))
    (x : NumberField.IdeleGroup (𝓞 F) F), A.RepresentsExteriorIdeal I x →
      A.idealGauss σ hS I p hp 1 * A.idealGauss σ hS I p hp 2 *
        (A.correctionTheta correction.Λ correction.G correction.η_id
          (QuotientGroup.mk x) : ℂ) = -η I.val

theorem unitQuotientClass_injective (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) :
    Function.Injective A.unitQuotientClass := by
  apply (injective_iff_map_eq_one A.unitQuotientClass).mpr
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hpow : A.diagonal u.val ∈ A.sixthPowers :=
      (QuotientGroup.eq_one_iff _).mp hq
    obtain ⟨g, hg⟩ := hpow
    have hlocal :
        (∀ w, ∃ b, b ^ 6 = (A.diagonal u.val).1 w) ∧
        (∀ v, ∃ b, b ^ 6 = (A.diagonal u.val).2 v) := by
      constructor
      · intro w
        exact ⟨g.1 w, congrArg (fun x : A.G => x.1 w) hg⟩
      · intro v
        exact ⟨g.2 v, congrArg (fun x : A.G => x.2 v) hg⟩
    obtain ⟨b, hb⟩ := A.local_power_injection F hCl 6 (by simp) u hlocal
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨b, hb⟩

theorem unitQuotientClass_range (A : SArithmeticData F) :
    A.unitQuotientClass.range = A.E := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H u =>
      exact ⟨A.diagonal u.val, ⟨u.val, u.property, rfl⟩, rfl⟩
  · rintro ⟨g, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' A.unitSixthPowers ⟨u, hu⟩, rfl⟩

theorem classGroup_subsingleton_of_principalization (A : SArithmeticData F)
    (hfrac : ∀ I : FractionalIdeal A.R⁰ F, IsUnit I →
      ∃ x : Fˣ, I = FractionalIdeal.spanSingleton A.R⁰ (x : F)) :
    Subsingleton (ClassGroup A.R) := by
  have hall : ∀ C : ClassGroup A.R, C = 1 := by
    intro C
    refine ClassGroup.induction F (fun I => ?_) C
    apply ClassGroup.mk_eq_one_iff.mpr
    obtain ⟨x, hx⟩ := hfrac I I.isUnit
    exact (FractionalIdeal.isPrincipal_iff _).mpr ⟨x, hx⟩
  exact ⟨fun C D => (hall C).trans (hall D).symm⟩

theorem principalIdealRing_of_classGroup_subsingleton (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) :
    IsPrincipalIdealRing A.R := by
  letI := hCl
  constructor
  intro J
  by_cases hJ : J = ⊥
  · subst J; exact bot_isPrincipal
  let E : A.Exterior := A.exteriorIdealEquiv.symm ⟨J, hJ⟩
  have hext : A.extendIdeal E = J := by
    rw [← A.exteriorIdealEquiv_apply]
    simp [E]
  have hO : IsUnit (E.val : FractionalIdeal (𝓞 F)⁰ F) :=
    isUnit_iff_ne_zero.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr E.property.1)
  have hunit : IsUnit (J : FractionalIdeal A.R⁰ F) := by
    rw [← hext]
    change IsUnit ((Ideal.map (algebraMap (𝓞 F) A.R) E.val : Ideal A.R) :
      FractionalIdeal A.R⁰ F)
    rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := F) F A.R E.val]
    exact hO.map (FractionalIdeal.extendedHom F A.R)
  exact ClassGroup.isPrincipal_of_isUnit_coeIdeal (K := F) J hunit

end SArithmeticData

theorem exists_principalizing_sArithmeticData_with_trace_bad_set
    (F : Type) [Field F] [NumberField F]
    (S₀ T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T → ResidueTrace.IsSelfDual v)
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (zeta12 : F) (hzeta12 : IsPrimitiveRoot zeta12 12) :
    ∃ A : SArithmeticData F,
      A.S₀ = S₀ ∧ A.modulus = 𝔪 ∧ A.zeta12 = zeta12 ∧
      A.ContainsTraceBadPlaces ∧
      (∀ I : FractionalIdeal A.R⁰ F, IsUnit I →
        ∃ x : Fˣ, I = FractionalIdeal.spanSingleton A.R⁰ (x : F)) := by
  obtain ⟨A, hbad, hmod, hζ, hfrac⟩ :=
    exists_principalizing_sArithmeticData F (S₀ ∪ T) 𝔪 h𝔪 zeta12 hzeta12
  let A' : SArithmeticData F := { A with
    S₀ := S₀
    bad_subset := by
      intro v hv
      exact A.bad_subset (hbad ▸ Finset.mem_union_left T hv) }
  refine ⟨A', rfl, hmod, hζ, ?_, hfrac⟩
  intro v hv
  apply hT v
  intro hvT
  apply hv
  exact A.bad_subset (hbad ▸ Finset.mem_union_right S₀ hvT)

theorem exists_generalArithmeticContext
    (F : Type) [Field F] [NumberField F]
    (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥)
    (zeta12 : F) (hzeta12 : IsPrimitiveRoot zeta12 12)
    (σ : F →+* ℂ) (η : RayClassCharacter F 𝔪) :
    ∃ (A : SArithmeticData F), A.S₀ = S₀ ∧ A.zeta12 = zeta12 ∧
      ∃ (hmod : A.modulus = 𝔪) (hS : A.ContainsTraceBadPlaces),
        Nonempty (A.GeneralArithmeticContext σ (hmod.symm ▸ η) hS) := by
  obtain ⟨T, hT⟩ := ArithmeticContext.exists_trace_exclusion_set F
  obtain ⟨A, hbad, hmod, hζ, hS, hfrac⟩ :=
    exists_principalizing_sArithmeticData_with_trace_bad_set
      F S₀ T hT 𝔪 h𝔪 zeta12 hzeta12
  have hCl := A.classGroup_subsingleton_of_principalization hfrac
  obtain ⟨D⟩ := SArithmeticData.exists_gaussCorrectionOutput
     A hCl hS σ (hmod.symm ▸ η)
  obtain ⟨hE, htwo, hthree⟩ :=
    ArithmeticContext.actual_hilbert_lagrangian_properties
      A hCl D.H D.B D.H_actual D.B_complement
  refine ⟨A, hbad, hζ, hmod, hS, ⟨{
    principal := A.principalIdealRing_of_classGroup_subsingleton hCl
    classGroup_trivial := hCl
    fractional_principal := hfrac
    unit_injective := A.unitQuotientClass_injective hCl
    unit_image := A.unitQuotientClass_range
    correction := D
    units_lagrangian := hE
    primary_two := htwo
    primary_three := hthree
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A D.H D.B D.H_actual D.B_complement
    allowed_integral := fun I =>
      A.exists_allowed_integral_generator hCl D.H D.B D.B_complement I
    allowed_unique := fun I a b ha hb =>
      A.allowed_generator_unique_mod_sixth hCl D.H D.B D.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }⟩⟩

end
end DedekindZetaZeroFree
