module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.LocalCyclicity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactSublevels.SchurLemma
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactOpenFixedSpaces

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open MomentSources KPGlobalResidualConstruction KPRankOneShellRepair
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev actualFiniteRepresentation (q : KPFinitePlace F) :=
  actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12 q
    (M q).inducing (M q).inducing.polarization (M q).haar (M q).haar_integer

def actualLocalAlgebra (v : KPHilbert.Place F) : Subalgebra ℂ (Module.End ℂ (actualLocal R M v)) :=
  match v with
  | .inl _ => NativeComplexHCSource.algebra NativeComplexHCOperators.operators
  | .inr q => NativeRepresentationAlgebra.algebra (actualFiniteRepresentation R M q)

instance (v : KPHilbert.Place F) : Module (actualLocalAlgebra R M v) (actualLocal R M v) :=
  Module.compHom _ (actualLocalAlgebra R M v).val.toRingHom
instance (v : KPHilbert.Place F) : IsScalarTower ℂ (actualLocalAlgebra R M v) (actualLocal R M v) :=
  ⟨fun _ _ _ => rfl⟩
instance (v : KPHilbert.Place F) : SMulCommClass (actualLocalAlgebra R M v) ℂ (actualLocal R M v) :=
  ⟨fun a c x => a.val.map_smul c x⟩

theorem actualLocalAlgebra_simple (v : KPHilbert.Place F) :
    IsSimpleOrder (Submodule (actualLocalAlgebra R M v) (actualLocal R M v)) := by
  cases v with
  | inl w => exact NativeComplexHCAlgebraic.native_operators_simple
  | inr q =>
    letI := (ActualSourcePredicates.actual_images_irreducible_of_length F R.A.zeta12
      R.A.primitive_zeta12 q (M q).inducing (M q).inducing.polarization
      (M q).haar (M q).haar_integer).1.2
    exact NativeRepresentationAlgebra.simple (actualFiniteRepresentation R M q)

instance actualLocalAlgebra_nontrivial (v : KPHilbert.Place F) : Nontrivial (actualLocal R M v) := by
  letI := actualLocalAlgebra_simple R M v
  exact (Submodule.nontrivial_iff (actualLocalAlgebra R M v)).mp inferInstance

instance actualLocalAlgebra_isSimpleModule (v : KPHilbert.Place F) :
    IsSimpleModule (actualLocalAlgebra R M v) (actualLocal R M v) :=
  (isSimpleModule_iff _ _).mpr (actualLocalAlgebra_simple R M v)

theorem actualFiniteAlgebra_scalar (q : KPFinitePlace F) :
    ∀ T : Module.End (actualLocalAlgebra R M (.inr q)) (actualLocal R M (.inr q)),
      ∃ c : ℂ, ∀ f, T f = c • f := by
  let A := (M q).inducing.borel
  let P := (M q).inducing.polarization
  let ρ := actualFiniteRepresentation R M q
  letI := (ActualSourcePredicates.actual_images_irreducible_of_length F R.A.zeta12
    R.A.primitive_zeta12 q (M q).inducing P (M q).haar (M q).haar_integer).1.2
  letI : T2Space (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :=
    (KPPGLLocalCover.finite_topological_cover F R.A.zeta12 R.A.primitive_zeta12 q
      (KPAdelicCoverRestrictedProduct.depth F R.A.zeta12 R.A.primitive_zeta12 q)
      (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 q)).1
  have hs : SmoothRepresentation ρ := by
    intro f
    obtain ⟨J, hJ⟩ := f.val.property.2
    exact ⟨J, fun j hj => Subtype.ext (Subtype.ext (hJ j hj))⟩
  apply NativeRepresentationAlgebra.scalar_commutant_of_compact_sublevels ρ hs
    (M q).inducing.iwasawa.compact
  intro J hJ
  letI : AddCommGroup (KPLocalPrincipalSeries.sectionSpace A P .minus 0) := inferInstance
  letI := NativeLocalFixedFinite.principal_series_fixed_finite A P
    (M q).inducing.iwasawa .minus 0 J hJ
  let inc : (fixedSubmodule ρ J.toOpenSubgroup.toSubgroup) →ₗ[ℂ]
      fixedSubmodule (KPLocalPrincipalSeries.IMinus A P) J.toOpenSubgroup.toSubgroup :=
    { toFun := fun f => ⟨f.val.val, fun j => congrArg Subtype.val (f.property j)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Finite.of_injective inc
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun f => f.val) h

theorem actualLocalAlgebra_scalar : RestrictedTensorSimple.ScalarCommutant
    (actualLocal R M) (fun v => actualLocalAlgebra R M v) := by
  intro v
  cases v with
  | inl w => exact NativeComplexHCAlgebraic.native_operators_scalar
  | inr q => exact actualFiniteAlgebra_scalar R M q

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
