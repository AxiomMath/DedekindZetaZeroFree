module

public import DedekindZetaZeroFree.Moments.Probes.PrincipalThetaContext

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalProbeConstruction
variable {F : Type} [Field F] [NumberField F]

structure ArithmeticBinding (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS)
    (G : ThetaBranch.AllowedRecipe A) (D : ComparisonPoissonCoefficientData F A) : Prop where
  sameComplement : G.B = C.correction.B
  sameGenerator : ∀ I, (G.generator I : F) = (D.generator I : F)
  exteriorCharacters : ∀ (I : A.Exterior) (a t : A.R), A.Generates I a →
    D.character a (FiniteTransform.residueMap A.R.toSubring a t) =
      NormalizedProbe.exteriorSexticRowCharacter A σ I t
  theta : ∀ m : ThetaReflectionData.Row A,
    D.theta m.val = (A.correctionLS C.correction.Λ C.correction.G 1
      (A.diagonal (ThetaReflectionData.rowUnit A m)) : ℂ)
  gammaTwo : ThetaReflectionData.GammaTwoCompatibility A D
  sixthUnits : ThetaReflectionData.SixthUnitCharacterCompatibility A D
  fieldTrace : ∀ x : F, D.additiveCharacter x = (A.fieldTraceCharacter x : ℂ)
  sameTrace : ∀ x : F, D.additiveCharacter x =
    ProbeAdditive.phase F A.Sf (fun v => ResidueTrace.localTraceCharacter v.val)
      (sLocalDiagonal F A.Sf x)

theorem exists_arithmetic_binding (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (C : A.GeneralArithmeticContext σ η hS) (hη : η.IsPrincipal)
    (principalIdele : C.correction.η_id = 1) :
    ∃ (G : ThetaBranch.AllowedRecipe A) (D : ComparisonPoissonCoefficientData F A),
      ArithmeticBinding A σ η hS C G D := by
  classical
  choose r a hr har ha using C.allowed_integral
  let G : ThetaBranch.AllowedRecipe A := {
    B := C.correction.B
    complement := C.correction.B_complement.1
    unit_kernel := Inputs.unit_kernel A C.classGroup_trivial
    generator := a
    generates := fun I => ⟨r I, hr I, har I⟩
    allowed := ha }
  let e : AddChar F ℂ := {
    toFun := fun x => (A.fieldTraceCharacter x : ℂ)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      exact congrArg Circle.coeHom (A.fieldTraceCharacter.map_add_eq_mul x y) }
  let D0 : ComparisonPoissonCoefficientData F A := {
    generator := r
    generates := hr
    finiteResidue := Inputs.finiteResidue A
    character := Inputs.rowCharacter A σ
    additiveCharacter := e
    gammaTwo := fun _ => 0
    theta := fun m => if hm : m ≠ 0 then
      (A.correctionLS C.correction.Λ C.correction.G 1
        (A.diagonal (ThetaReflectionData.rowUnit A ⟨m, hm⟩)) : ℂ) else 0 }
  let D : ComparisonPoissonCoefficientData F A :=
    { D0 with gammaTwo := ThetaReflectionData.gammaTwoRecipe A D0 }
  refine ⟨G, D, rfl, har, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Inputs.rowCharacter_apply A σ
  · intro m
    exact dif_pos m.property
  · intro c
    rfl
  · intro c n u
    apply Inputs.rowCharacter_sixth
    exact mul_ne_zero (hr c.val).1 (pow_ne_zero 3 (hr n).1)
  · intro x
    rfl
  · exact Inputs.fieldTrace_phase A

theorem exists_enlarged_principal_context
    (S : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F S.modulus) (hη : η.IsPrincipal) :
    ∃ A : SArithmeticData F, S.Sf ⊆ A.Sf ∧ A.zeta12 = S.zeta12 ∧
      ∃ (hmod : A.modulus = S.modulus) (hS : A.ContainsTraceBadPlaces),
        PoissonS.ContainsDifferent F A.Sf ∧
        ∃ C : A.GeneralArithmeticContext σ (hmod.symm ▸ η) hS,
          C.correction.η_id = 1 := by
  classical
  let T := (Ideal.finite_factors ((differentIdeal_ne_bot : differentIdeal ℤ (𝓞 F) ≠ ⊥))).toFinset
  obtain ⟨A, hbad, hroot, hmod, hS, ⟨C⟩⟩ := exists_generalArithmeticContext
     F (S.Sf ∪ T) S.modulus S.modulus_ne_zero S.zeta12 S.primitive_zeta12 σ η
  have hηA : (hmod.symm ▸ η).IsPrincipal := by
    have transport : ∀ (m n : Ideal (𝓞 F)) (h : m = n)
        (η : RayClassCharacter F n), η.IsPrincipal → (h.symm ▸ η).IsPrincipal := by
      intro m n h
      subst n
      exact fun _ hη => hη
    exact transport _ _ hmod η hη
  refine ⟨A, ?_, hroot, hmod, hS, ?_, Inputs.principalContext A σ _ hS C hηA, rfl⟩
  · intro v hv
    exact A.bad_subset (hbad ▸ Finset.mem_union_left T hv)
  · intro v hv
    apply A.bad_subset
    rw [hbad]
    apply Finset.mem_union_right
    exact (Set.Finite.mem_toFinset _).mpr hv

end DedekindZetaZeroFree.PrincipalProbeConstruction

end
