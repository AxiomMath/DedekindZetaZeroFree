module

public import DedekindZetaZeroFree.Theta.Periods.ArchimedeanTensorProduct
public import DedekindZetaZeroFree.Adeles.Lattices.ArchimedeanDiagonalInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open LiteralSource MomentSources HCGeneration TensorActionSource KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
variable (μ : ∀ q : KPFinitePlace F, Measure (q.adicCompletion F))
variable [hhaar : ∀ q, (μ q).IsAddHaarMeasure]
variable (hμ : ∀ q, μ q ((ValuativeRel.valuation (q.adicCompletion F)).integer : Set _) = 1)
local notation "H" => actualImageData R P C μ hμ
local notation "W" => actualLocal R H
local notation "E" => bad R.A P C
local notation "e" => actualReference R P C μ hμ
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open CurrentOutputExtension KPCplxActualImage KPCplxWhittakerUnique
open RootDerivatives KPReferenceChange.StandardComplexImage

theorem actual_spherical_arch_product (N : TraceHaarTransport R)

    (s : RestrictedTensorSimple.Level E) (x : ∀j:s.val,W j.val)
    (hw : ∀w:InfinitePlace F,Sum.inl w∈s.val)
    (hx : ∀w,x ⟨Sum.inl w,hw w⟩=sphericalCoreSeed)
    (L : InfinitePlace F → Theta traceFrequency →L[ℂ] ℂ)
    (hL : ∀w,L w∈whittakerSpace traceFrequency traceCharacter)
    (hn : ∀w,L w sphericalSeed≠0)
    (h1 : actualStagePeriod R P C μ hμ N s x 1=∏w,L w sphericalSeed)
    (y : R.A.G) :
    actualStagePeriod R P C μ hμ N s x (MomentSources.diagonal R (y.1,1)) =
      ∏w,L w (KPReferenceChange.StandardComplexImage.action R.A w
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) (y.1 w)) sphericalSeed) := by
  have hv : ∀w,L w (harmonicInclusion (x ⟨Sum.inl w,hw w⟩))≠0 := by
    intro w
    rw [hx]
    exact hn w
  have he := actualStage_arch_product R P C μ hμ N  s x hw L hL hv
    (fun w=>Matrix.ProjGenLinGroup.mk (actualArchDiagonal R y w)) Finset.univ 1
    (by intro w; simp)
  simp only [archPartial_univ,one_mul,hx] at he
  rw [diagonal_arch_insertion]
  rw [he,h1,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  rw [diagonal_standard_action]
  change (L w (imageAction traceFrequency _ sphericalSeed)/L w sphericalSeed)*L w sphericalSeed=_
  exact div_mul_cancel₀ _ (hn w)
end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
