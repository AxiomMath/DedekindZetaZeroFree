module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.NormalizedProbeArithmeticData
public import DedekindZetaZeroFree.Arithmetic.Kummer.QuadraticCharacterFamilyAndConductorShape

@[expose] public section

namespace DedekindZetaZeroFree.PrincipalMellinGrowth

open scoped NumberField Classical nonZeroDivisors
open ThetaBranch ThetaPhaseSeparation

variable {F : Type} [Field F] [NumberField F]

 noncomputable def recipeContext
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) :
    R.A.GeneralArithmeticContext R.σ R.target R.traceBad := by
  let A := R.A
  let D := R.probe.correction
  letI := R.classKilled
  obtain ⟨hE, htwo, hthree⟩ :=
    ArithmeticContext.actual_hilbert_lagrangian_properties
      A R.classKilled D.H D.B D.H_actual D.B_complement
  exact {
    principal := A.principalIdealRing_of_classGroup_subsingleton R.classKilled
    classGroup_trivial := R.classKilled
    fractional_principal := fun I hI => exists_unit_of_isPrincipal I
      (ClassGroup.isPrincipal_coeSubmodule_of_isUnit I hI) hI.ne_zero
    unit_injective := A.unitQuotientClass_injective R.classKilled
    unit_image := A.unitQuotientClass_range
    correction := D
    units_lagrangian := hE
    primary_two := htwo
    primary_three := hthree
    reciprocity := ArithmeticContext.actual_hilbert_sextic_reciprocity
      A D.H D.B D.H_actual D.B_complement
    allowed_integral := fun I =>
      A.exists_allowed_integral_generator R.classKilled D.H D.B D.B_complement I
    allowed_unique := fun I a b ha hb =>
      A.allowed_generator_unique_mod_sixth R.classKilled D.H D.B D.B_complement I a b ha hb
    normOne_compact := ArithmeticContext.normOne_sixth_unit_quotient_compact A
    prime_target := fun I v hIv p hp a ha hap x hx =>
      D.prime_theta I v hIv p hp a ha hap x hx }

 def exteriorFamily (A : SArithmeticData F)
    (𝓕 : QuadraticHeckeFamily F (uniformSquareUnitModulus A.Sf)) :
    QuadraticHeckeFamily F A.cS where
  cond := 𝓕.cond
  χ := 𝓕.χ
  primitive := fun c hc hcop => 𝓕.primitive c hc ((KummerSquarefreeMembers.exterior_iff A c).mpr hcop)
  quadratic := fun c d hc hcop => 𝓕.quadratic c d hc ((KummerSquarefreeMembers.exterior_iff A c).mpr hcop)
  G := 𝓕.G
  instGroup := 𝓕.instGroup
  instFinite := 𝓕.instFinite
  cls := 𝓕.cls
  cls_top := 𝓕.cls_top
  cls_mul := fun c d hc hd => 𝓕.cls_mul c d
    ((KummerSquarefreeMembers.exterior_iff A c).mpr hc)
    ((KummerSquarefreeMembers.exterior_iff A d).mpr hd)
  C := 𝓕.C
  C_sq := 𝓕.C_sq
  reciprocity := fun c d hc hcopc hd hcopd => 𝓕.reciprocity c d hc
    ((KummerSquarefreeMembers.exterior_iff A c).mpr hcopc) hd
    ((KummerSquarefreeMembers.exterior_iff A d).mpr hcopd)
  product_primitive := fun c d hc hcopc hd hcopd => 𝓕.product_primitive c d hc
    ((KummerSquarefreeMembers.exterior_iff A c).mpr hcopc) hd
    ((KummerSquarefreeMembers.exterior_iff A d).mpr hcopd)

private theorem char_one (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (t : A.R) :
    A.sexticResiduePowerChar σ I 1 (Ideal.Quotient.mk (A.extendIdeal I) t) =
      σ (A.sexticResidue I t) := by
  have hp : SArithmeticData.sexticExponent (1 : ℤ) = 1 := by decide
  simp only [SArithmeticData.sexticResiduePowerChar, hp, pow_one]
  by_cases hx : IsUnit (Ideal.Quotient.mk (A.extendIdeal I) t)
  · change _ = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [← hx.unit_spec, MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    rfl
  · rw [MulChar.map_nonunit _ hx]
    change 0 = σ (MulChar.ofUnitHom (A.sexticResidueFamily I) _)
    rw [MulChar.map_nonunit _ hx, map_zero]

private theorem idealSymbol_eq_residue (A : SArithmeticData F) (G : AllowedRecipe A)
    (σ : F →+* ℂ) (d c : A.Exterior) (hd : Squarefree d.val)
    (r : A.R) (hr : (G.generator c : F) = (r : F)) :
    idealSymbol A σ d (G.generator c) = σ (A.sexticResidue d r) := by
  have hr0 : r ≠ 0 := by
    intro h
    exact (G.generator c).ne_zero (hr.trans (by simp [h]))
  have he : ThetaReflectionData.rowUnit A ⟨r, hr0⟩ = G.generator c :=
    Units.ext hr.symm
  have h := (NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar A σ d r).trans
    (char_one A σ d r)
  rw [NormalizedProbe.exteriorSexticRowCharacter, dif_neg hr0, he] at h
  rw [← h]
  unfold idealSymbol
  apply Finset.prod_congr rfl
  intro p hp
  have hexp : idealPrimeExponent p.val.asIdeal d.val = 1 := by
    apply Multiset.count_eq_one_of_mem
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors d.property.1).mp hd)
    simpa only [support, Finset.mem_preimage, idealPrimeSupport, Multiset.mem_toFinset] using p.property
  rw [hexp, pow_one]
  rfl

private theorem chosen_residue_eq
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (c d : R.A.Exterior)
    (r : R.A.R) (hgen : R.A.Generates c r)
    (hr : (R.probe.allowed.generator c : F) = (r : F)) :
    KummerExteriorValues.sexticValue R.A R.σ R.target R.traceBad (recipeContext R) c d =
      R.σ (R.A.sexticResidue d r) := by
  let C := recipeContext R
  let a := KummerSquarefreeMembers.chooseRepresentative R.A R.σ R.target R.traceBad C c
  have hallow : R.A.IsAllowed C.correction.B (R.probe.allowed.generator c) := by
    change R.A.sClass (R.probe.allowed.generator c) ∈ R.probe.correction.B
    rw [← R.probe.sameComplement]
    exact R.probe.allowed.allowed c
  have hG : R.A.IsAllowedGenerator C.correction.B
      (R.A.extendIdeal c : FractionalIdeal R.A.R⁰ F) (R.probe.allowed.generator c) := by
    refine ⟨?_, hallow⟩
    rw [← hgen.2, FractionalIdeal.coeIdeal_span_singleton]
    change FractionalIdeal.spanSingleton R.A.R⁰ (r : F) = _
    rw [← hr]
  obtain ⟨u, hu, he⟩ := C.allowed_unique _ _ _ a.isAllowedGenerator hG
  change u ^ 6 = a.radical / R.probe.allowed.generator c at he
  have heq : a.integral = r * (R.A.unitEquiv ⟨u, hu⟩ : R.A.R) ^ 6 := by
    apply Subtype.ext
    change (a.integral : F) = (r : F) * ((R.A.unitEquiv ⟨u, hu⟩ : R.A.R) : F) ^ 6
    have hf : a.radical = R.probe.allowed.generator c * u ^ 6 := by
      rw [he, mul_div_cancel]
    have huF : ((R.A.unitEquiv ⟨u, hu⟩ : R.A.R) : F) = (u : F) := rfl
    rw [huF, ← a.radical_eq, ← hr, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hf]
  change R.σ (R.A.sexticResidue d a.integral) = _
  rw [heq, R.A.sexticResidue_sixth_unit_translate]

theorem actual_quadratic_family_exists
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) :
    ∃ 𝓕 : QuadraticHeckeFamily F R.A.cS,
      RMRetainedAggregation.QuadraticFamilyCompatibility
        R.A R.probe.allowed R.σ 𝓕 := by
  classical
  have h12 : (primitiveRoots 12 F).Nonempty :=
    ⟨R.A.zeta12, (mem_primitiveRoots (by norm_num)).mpr R.A.primitive_zeta12⟩
  obtain ⟨_, _, 𝓕, h𝓕⟩ := RMKummerFamily.exists_actualKummerFamily
    h12 R.A R.σ R.target R.traceBad (recipeContext R)
  refine ⟨exteriorFamily R.A 𝓕, ?_⟩
  intro d c
  have hc : c.val.val ⊔ uniformSquareUnitModulus R.A.Sf = ⊤ :=
    (KummerSquarefreeMembers.exterior_iff R.A c.val.val).mpr c.val.property.2
  have hd : d.val.val ⊔ uniformSquareUnitModulus R.A.Sf = ⊤ :=
    (KummerSquarefreeMembers.exterior_iff R.A d.val.val).mpr d.val.property.2
  have hvalue := h𝓕.2.2.2.2.2.2.2.1 c.val.val c.property hc
    d.val.val d.val.property.1 hd
  change 𝓕.χ c.val.val d.val.val = _
  have hic : KummerSquarefreeMembers.exteriorIndex R.A c.val.val c.property hc = c.val :=
    Subtype.ext rfl
  have hid : KummerExteriorValues.exteriorIndex R.A d.val.val d.val.property.1 hd = d.val :=
    Subtype.ext rfl
  rw [hic, hid] at hvalue
  rw [hvalue]
  by_cases hcop : d.val.val ⊔ c.val.val = ⊤
  · obtain ⟨r, hgen, hr⟩ := R.probe.allowed.generates c.val
    rw [KummerExteriorValues.cubicSexticValue,
      chosen_residue_eq R c.val d.val r hgen hr,
      quadraticPairing, if_pos hcop,
      idealSymbol_eq_residue R.A R.probe.allowed R.σ d.val c.val d.property r hr]
  · have hzero := KummerExteriorValues.cubicSexticValue_shared_zero
      R.A R.σ R.target R.traceBad (recipeContext R) d.val c.val hcop
    rw [hzero.2, quadraticPairing, if_neg hcop]

end DedekindZetaZeroFree.PrincipalMellinGrowth
