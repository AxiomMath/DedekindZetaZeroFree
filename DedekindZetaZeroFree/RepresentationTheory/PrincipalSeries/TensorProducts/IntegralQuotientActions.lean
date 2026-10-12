module

public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorRealization.LocalRangeQuotients

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)

abbrev plusLocal : KPHilbert.Place F → Type
  | Sum.inl _ => KPLiteralTensor.harmonicPlus
  | Sum.inr q => KPLocalPrincipalSeries.sectionSpace (M q).inducing.borel
      (M q).inducing.polarization .plus 0

instance plusLocalAdd (p : KPHilbert.Place F) : AddCommGroup (plusLocal R M p) := by
  cases p <;> infer_instance
instance plusLocalModule (p : KPHilbert.Place F) : Module ℂ (plusLocal R M p) := by
  cases p <;> infer_instance

def finiteSourceQuotient (q : KPFinitePlace F) :
    plusLocal R M (Sum.inr q) →ₗ[ℂ] actualLocal R M (Sum.inr q) :=
  (KPRankOneShellRepair.actualCanonicalForwardMap F R.A.zeta12 R.A.primitive_zeta12
    q (M q).inducing (M q).inducing.polarization (M q).haar (M q).haar_integer).toLinearMap.rangeRestrict

theorem finiteSourceQuotient_surjective (q : KPFinitePlace F) :
    Function.Surjective (finiteSourceQuotient R M q) := by
  rintro ⟨f, x, rfl⟩
  exact ⟨x, rfl⟩

def sourceQuotient (p : KPHilbert.Place F) : plusLocal R M p →ₗ[ℂ] actualLocal R M p := by
  cases p with
  | inl w => exact KPLiteralTensor.harmonicQuotient
  | inr q => exact finiteSourceQuotient R M q

theorem sourceQuotient_surjective (p : KPHilbert.Place F) :
    Function.Surjective (sourceQuotient R M p) := by
  cases p with
  | inl w => exact KPLiteralTensor.harmonicQuotient_surjective
  | inr q => exact finiteSourceQuotient_surjective R M q

def sourceStageQuotient (s : Finset (KPHilbert.Place F)) :
    RestrictedTensorSimple.Stage (plusLocal R M) s →ₗ[ℂ]
      RestrictedTensorSimple.Stage (actualLocal R M) s :=
  PiTensorProduct.map (fun p : s => sourceQuotient R M p)

theorem sourceStageQuotient_surjective (s : Finset (KPHilbert.Place F)) :
    Function.Surjective (sourceStageQuotient R M s) := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
      choose z hz using fun p : s => sourceQuotient_surjective R M p (x p)
      refine ⟨c • PiTensorProduct.tprod ℂ z, ?_⟩
      simp only [sourceStageQuotient, map_smul, PiTensorProduct.map_tprod]
      rw [show (fun p : s => sourceQuotient R M p (z p)) = x from funext hz]
  | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩

theorem harmonicSource_compact_mem (k : KPCplxCharacterHaar.ComplexSU2)
    (x : KPLiteralTensor.harmonicPlus) :
    KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.positiveParameter
      (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x.val ∈
      KPLiteralTensor.harmonicPlus := by
  let a := Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)
  have ha : a ∈ KPCplxPrincipalSeriesCharts.compactSubgroup := ⟨k, rfl⟩
  apply Submodule.iSup_induction
    (fun l : ℕ => KPCplxIntertwinerEigenvalues.harmonicKType
      KPCplxPrincipalSeriesCharts.positiveParameter l) x.property
    (motive := fun y => KPCplxPrincipalSeriesCharts.pi
      KPCplxPrincipalSeriesCharts.positiveParameter a y ∈ KPLiteralTensor.harmonicPlus)
  · intro l y hy
    exact Submodule.mem_iSup_of_mem l
      ((KPCplxIntertwinerEigenvalues.harmonicKType_multiplicity_one
        KPCplxPrincipalSeriesCharts.positiveParameter l).1 ⟨a, ha⟩ y hy)
  · rw [KPGlobalResidualConstruction.pi_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [KPGlobalResidualConstruction.pi_add]
    exact Submodule.add_mem _ hy hz

def harmonicSourceAction (k : KPCplxCharacterHaar.ComplexSU2) :
    KPLiteralTensor.harmonicPlus →ₗ[ℂ] KPLiteralTensor.harmonicPlus where
  toFun x := ⟨KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.positiveParameter
    (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x.val,
    harmonicSource_compact_mem k x⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    exact KPGlobalResidualConstruction.pi_add _ _ _ _
  map_smul' c x := by
    apply Subtype.ext
    simp only [SetLike.val_smul, RingHom.id_apply]
    exact KPGlobalResidualConstruction.pi_smul _ _ _ _

theorem harmonicSourceQuotient_intertwines (k : KPCplxCharacterHaar.ComplexSU2)
    (x : KPLiteralTensor.harmonicPlus) :
    KPLiteralTensor.harmonicQuotient (harmonicSourceAction k x) =
      KPGlobalResidualConstruction.complexCoreSU2Action k
        (KPLiteralTensor.harmonicQuotient x) := by
  apply Subtype.ext
  simp only [KPLiteralTensor.harmonicQuotient_val]
  change KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ)
      (KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.positiveParameter
        (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k)) x.val) =
    KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.negativeParameter
      (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k))
      (KPCplxIntertwinerEigenvalues.standardIntertwiner (1 : ℂˣ) x.val)
  exact KPCplxIntertwinerEigenvalues.standardIntertwiner_equivariant (1 : ℂˣ) _ x.val

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
