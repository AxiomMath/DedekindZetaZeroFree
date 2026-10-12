module

public import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField MeasureTheory ValuativeRel
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

abbrev exteriorImageAction (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (p : ThetaBranch.ExteriorPrime R.A) :=
  KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p.val (C.factorization.finiteData p.val).inducing
    (C.factorization.finiteData p.val).inducing.polarization
    (C.factorization.finiteData p.val).haar (C.factorization.finiteData p.val).haar_integer

abbrev exteriorDiagonal (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (y : (p.val.adicCompletion F)ˣ) :=
  KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)
    (KPRationalAdelicSplitting.ACoordinates F R.A.zeta12 R.A.primitive_zeta12
      (KPRationalAdelicSplitting.localIdele F (Sum.inr p.val) y) (Sum.inr p.val))

theorem exterior_diagonal_eq_standard_lift (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) (y : (p.val.adicCompletion F)ˣ) :
    exteriorDiagonal R p y = KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) y := by
  unfold exteriorDiagonal KPRationalAdelicSplitting.ACoordinates KPPGLLocalCover.A
  congr 2
  apply Units.ext
  change Pi.mulSingle p.val (y : p.val.adicCompletion F) p.val = (y : p.val.adicCompletion F)
  simp

def exteriorWhittakerValue (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N)
    (p : ThetaBranch.ExteriorPrime R.A) (y : (p.val.adicCompletion F)ˣ) : ℂ :=
  C.factorization.ell (Sum.inr p.val)
    (exteriorImageAction R C p (exteriorDiagonal R p y) (C.factorization.references (Sum.inr p.val)))

abbrev exteriorCompletionGenerator (R : PrincipalMellin.ActualRecipe S η)
    (p : ThetaBranch.ExteriorPrime R.A) : (p.val.adicCompletion F)ˣ :=
  Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom
    (R.probe.allowed.generator (ThetaBranch.primeIdeal R.A p))

theorem exterior_prime_not_mem_factorization_bad (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (p : ThetaBranch.ExteriorPrime R.A) :
    Sum.inr p.val ∉ C.factorization.bad := by
  intro hp
  rcases (C.factorization.bad_exact _).mp hp with ⟨w, hw⟩ | ⟨q, hq, hqS⟩
  · cases hw
  · have he : p.val = q := Sum.inr.inj hq
    exact p.property (he ▸ hqS)

theorem exterior_reference_value_eq_one (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) (p : ThetaBranch.ExteriorPrime R.A) :
    C.factorization.ell (Sum.inr p.val) (C.factorization.references (Sum.inr p.val)) = 1 :=
  C.factorization.reference_value _ (exterior_prime_not_mem_factorization_bad R C p)

def ExteriorWhittakerEquivariance (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) : Prop :=
  ∀ (p : ThetaBranch.ExteriorPrime R.A) (z : p.val.adicCompletion F)
    (b : actualLocal R C.factorization.finiteData (Sum.inr p.val)),
    C.factorization.ell (Sum.inr p.val)
      (exteriorImageAction R C p (KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) z) b) =
    (ResidueTrace.localTraceCharacter p.val z : ℂ) * C.factorization.ell (Sum.inr p.val) b

theorem exterior_whittaker_equivariance (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (C : JointHaarFactorizedSources R N) : ExteriorWhittakerEquivariance R C := by
  intro p z b
  exact ExteriorWhittakerValues.StoredWhittaker.ell_finite_root R C.factorization p.val z b

end DedekindZetaZeroFree.ThetaExpansion

end
