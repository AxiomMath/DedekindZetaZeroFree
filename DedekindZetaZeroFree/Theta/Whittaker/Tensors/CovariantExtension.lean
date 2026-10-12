module

public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CovariantAssembly
open MomentSources NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem update_instances {ι : Type} {β : ι → Type} (d e : DecidableEq ι)
    (f : ∀ i, β i) (i : ι) (b : β i) :
    @Function.update ι β d f i b = @Function.update ι β e f i b :=
  congrArg (fun deq => @Function.update ι β deq f i b) (Subsingleton.elim d e)

def add_finite (D : Generated R N) (h : ∀ q (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level D.bad) (hq : Sum.inr q ∈ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) g,
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
          (D.finiteData q).haar (D.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩))))) g =
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))) : FiniteCovariant R N where
  toGenerated := D
  finite_intertwining := by
    intro q a s hq x g
    let value : actualLocal R D.finiteData (Sum.inr q) :=
      KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q (D.finiteData q).inducing (D.finiteData q).inducing.polarization
        (D.finiteData q).haar (D.finiteData q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
        (x ⟨Sum.inr q,hq⟩)
    have hu := update_instances
      (@Subtype.instDecidableEq (KPHilbert.Place F) (fun j => j ∈ s.val)
        NonDegenerate.instDecidableEqPlace)
      (inferInstance : DecidableEq s.val) x ⟨Sum.inr q,hq⟩ value
    exact (congrArg (fun y : ∀ j : s.val, actualLocal R D.finiteData j.val =>
      D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ y)) g) hu).trans (h q a s hq x g)

def add_complex (D : FiniteCovariant R N) (h : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level D.bad) (hw : Sum.inl w ∈ s.val)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) g,
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w, hw⟩
        (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))))) g =
    D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)) : ComplexCovariant R N where
  toFiniteCovariant := D
  complex_intertwining := by
    have hd : (NonDegenerate.instDecidableEqPlace : DecidableEq (KPHilbert.Place F)) =
        (inferInstance : DecidableEq (KPHilbert.Place F)) := Subsingleton.elim _ _
    rw [hd]
    exact h

end DedekindZetaZeroFree.FourierContinuation.CovariantAssembly

end
