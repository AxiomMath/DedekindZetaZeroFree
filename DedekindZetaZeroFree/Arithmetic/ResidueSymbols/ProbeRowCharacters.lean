module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Sextic.PrincipalExteriorCharacter

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.PrincipalProbeConstruction.Inputs
variable {F : Type} [Field F] [NumberField F]

def rowIdeal (A : SArithmeticData F) (a : A.R) (ha : a ≠ 0) : A.Exterior :=
  A.exteriorIdealEquiv.symm ⟨Ideal.span {a}, fun h => ha (Ideal.span_singleton_eq_bot.mp h)⟩

theorem rowIdeal_generates (A : SArithmeticData F) (a : A.R) (ha : a ≠ 0) :
    A.Generates (rowIdeal A a ha) a := by
  refine ⟨ha, ?_⟩
  rw [← A.exteriorIdealEquiv_apply]
  simp [rowIdeal]

def rowCharacter (A : SArithmeticData F) (σ : F →+* ℂ) (a : A.R) :
    MulChar (FiniteTransform.Residue A.R.toSubring a) ℂ := by
  classical
  by_cases ha : a = 0
  · exact 1
  · let I := rowIdeal A a ha
    let e := Ideal.quotientEquivAlgOfEq A.R (rowIdeal_generates A a ha).2
    exact {
      toFun := fun x => A.sexticResiduePowerChar σ I 1 (e x)
      map_one' := by simp
      map_mul' := by intros; simp
      map_nonunit' := by
        intro x hx
        exact MulChar.map_nonunit _ (fun h => hx (by simpa using h.map e.symm.toMonoidHom)) }

theorem rowCharacter_apply (A : SArithmeticData F) (σ : F →+* ℂ)
    (I : A.Exterior) (a t : A.R) (ha : A.Generates I a) :
    rowCharacter A σ a (FiniteTransform.residueMap A.R.toSubring a t) =
      NormalizedProbe.exteriorSexticRowCharacter A σ I t := by
  have hI : rowIdeal A a ha.1 = I := by
    apply A.exteriorIdealEquiv.injective
    apply Subtype.ext
    simp only [rowIdeal, Equiv.apply_symm_apply]
    simpa only [A.exteriorIdealEquiv_apply] using ha.2
  rw [rowCharacter, dif_neg ha.1]
  change A.sexticResiduePowerChar σ (rowIdeal A a ha.1) 1
    (Ideal.Quotient.mk _ t) = _
  rw [hI]
  exact (NormalizedProbe.exteriorSexticRowCharacter_eq_sexticResiduePowerChar A σ I t).symm

def finiteResidue (A : SArithmeticData F) (a : A.R) (ha : a ≠ 0) :
    Fintype (FiniteTransform.Residue A.R.toSubring a) := by
  let I := rowIdeal A a ha
  letI := A.exteriorResidue_finite I
  let e := Ideal.quotientEquivAlgOfEq A.R (rowIdeal_generates A a ha).2
  letI : Finite (FiniteTransform.Residue A.R.toSubring a) := Finite.of_equiv _ e.toEquiv.symm
  exact Fintype.ofFinite _

theorem rowCharacter_sixth (A : SArithmeticData F) (σ : F →+* ℂ)
    (a : A.R) (ha : a ≠ 0) (u : A.Rˣ) :
    rowCharacter A σ a (FiniteTransform.residueMap A.R.toSubring a ((u : A.R) ^ 6)) = 1 := by
  rw [rowCharacter, dif_neg ha]
  let I := rowIdeal A a ha
  let e := Ideal.quotientEquivAlgOfEq A.R (rowIdeal_generates A a ha).2
  let v : (A.R ⧸ A.extendIdeal I)ˣ :=
    Units.map (Ideal.Quotient.mk (A.extendIdeal I)).toMonoidHom u
  change A.sexticResiduePowerChar σ I 1 ((v ^ 6 : (A.R ⧸ A.extendIdeal I)ˣ) : _) = 1
  unfold SArithmeticData.sexticResiduePowerChar
  rw [MulChar.pow_apply_coe, MulChar.ofUnitHom_coe]
  have h6 := congrArg (Units.map σ.toMonoidHom) (A.sexticResidueFamily_normalized.1 I v)
  simp only [map_pow, map_one] at h6
  simpa only [map_pow, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, Units.val_one,
    one_pow] using congrArg (fun z : ℂˣ => (z : ℂ) ^ SArithmeticData.sexticExponent 1) h6

theorem fieldTrace_phase (A : SArithmeticData F) (x : F) :
    (A.fieldTraceCharacter x : ℂ) =
      ProbeAdditive.phase F A.Sf (fun v => ResidueTrace.localTraceCharacter v.val)
        (sLocalDiagonal F A.Sf x) := by
  have harch (y : InfiniteAdeleRing F) :
      ProbeAdditive.archPhase F y = ∏ w, (archTraceCharacter w (y w) : ℂ) := by
    simp only [archTraceCharacter_of_isComplex _ (A.complex_place _), Circle.coe_exp,
      InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
    rw [ProbeAdditive.archPhase, ← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_ofNat]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  change (Circle.coeHom ((∏ w, archTraceCharacter w ((sLocalDiagonal F A.Sf x).1 w)) *
    ∏ v : A.Sf, ResidueTrace.localTraceCharacter v.val ((sLocalDiagonal F A.Sf x).2 v))) = _
  rw [map_mul, map_prod, map_prod]
  exact congrArg (fun z => z * _) (harch _).symm

theorem unit_kernel (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R)) :
    A.U ⊓ (ThetaReflectionData.rationalClass A).ker = ThetaReflectionData.rationalGamma A := by
  apply le_antisymm
  · intro x hx
    have hq : A.unitQuotientClass (QuotientGroup.mk' A.unitSixthPowers ⟨x, hx.1⟩) = 1 := hx.2
    have heq := A.unitQuotientClass_injective hCl (hq.trans (map_one _).symm)
    obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp heq
    refine ⟨u.val, u.property, ?_⟩
    exact congrArg Subtype.val hu
  · intro x hx
    refine ⟨?_, ThetaReflectionData.rationalGamma_le_class_ker A hx⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact A.U.pow_mem hu 6

end DedekindZetaZeroFree.PrincipalProbeConstruction.Inputs

end
