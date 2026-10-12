module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.LocalDiagonalGeometry
public import DedekindZetaZeroFree.Theta.Whittaker.LocalFunctionalsFromGlobalPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

structure PreparedSphericalTensor (D : SourceFactorization R Q T) where
  stage : RestrictedTensorSimple.Level D.bad
  entries : ∀ p : stage.val, actualLocal R D.finiteData p
  stage_exact : stage.val = D.bad
  spherical : ∀ (w : InfinitePlace F) (hw : Sum.inl w ∈ stage.val),
    entries ⟨Sum.inl w, hw⟩ = sphericalCoreSeed
  finite_value : ∀ (q : R.A.Sf) (hq : Sum.inr q.val ∈ stage.val),
    D.ell (Sum.inr q.val) (entries ⟨Sum.inr q.val, hq⟩) = 1
  nonzero : tensorFunction R D stage entries ≠ 0
  neighborhood : ∀ q : R.A.Sf, Set (q.val.adicCompletion F)ˣ
  open_neighborhood : ∀ q, IsOpen (neighborhood q)
  one_neighborhood : ∀ q, 1 ∈ neighborhood q
  finite_fixed : ∀ (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ),
    (∀ q, u q ∈ neighborhood q) → ∀ (l : List R.A.Sf) (g : Group R),
      tensorFunction R D stage entries (g * finiteDiagonalWord R l u) =
        tensorFunction R D stage entries g

theorem prepared_spherical_tensor_exists (D : SourceFactorization R Q T) :
    Nonempty (PreparedSphericalTensor R D) := by
  obtain ⟨s, x, hs, harch, hfin, _, _, _, hne⟩ := spherical_frozen_tensor R D
  obtain ⟨V, hVo, hV1, hfix⟩ := tensor_finite_common_neighborhood R D s x
  exact ⟨{
    stage := s
    entries := x
    stage_exact := hs
    spherical := harch
    finite_value := hfin
    nonzero := hne
    neighborhood := V
    open_neighborhood := hVo
    one_neighborhood := hV1
    finite_fixed := hfix }⟩

namespace PreparedSphericalTensor
variable {R} {D : SourceFactorization R Q T} (P : PreparedSphericalTensor R D)

def value : Functions R := _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D P.stage P.entries

theorem period_integrable (g : Group R) :
    Integrable (fun q => P.value
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq :=
  core_period_integrable R D _ g

theorem product_at_one : fourier R Q.dq P.value 1 =
    ∏ p : P.stage.val, D.ell p (P.entries p) := D.product_exact _ _

theorem complex_compact (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) (g : Group R) :
    P.value (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12
      R.A.primitive_zeta12 w k) = P.value g := by
  have hw : Sum.inl w ∈ P.stage.val := by
    rw [P.stage_exact]
    exact (D.bad_exact _).mpr (Or.inl ⟨w, rfl⟩)
  exact tensorFunction_spherical_compact R D P.stage P.entries w hw (P.spherical w hw) k g

theorem diagonal_near_pointwise (y : R.A.G)
    (hy : ∀ q : R.A.Sf, y.2 q ∈ P.neighborhood q) (g : Group R) :
    P.value (g * diagonal R y) = P.value (g * diagonal R (y.1, 1)) := by
  rw [diagonal_arch_finite, ← mul_assoc]
  exact P.finite_fixed y.2 hy Finset.univ.toList _

theorem diagonal_near_period (y : R.A.G)
    (hy : ∀ q : R.A.Sf, y.2 q ∈ P.neighborhood q) :
    Integrable (fun q => P.value
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * diagonal R y) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq ∧
    Integrable (fun q => P.value
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) *
        diagonal R (y.1, 1)) * star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq ∧
    fourier R Q.dq P.value (diagonal R y) = fourier R Q.dq P.value (diagonal R (y.1, 1)) := by
  refine ⟨P.period_integrable _, P.period_integrable _, ?_⟩
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [P.diagonal_near_pointwise y hy]

end PreparedSphericalTensor

end DedekindZetaZeroFree.RootDerivatives

end
