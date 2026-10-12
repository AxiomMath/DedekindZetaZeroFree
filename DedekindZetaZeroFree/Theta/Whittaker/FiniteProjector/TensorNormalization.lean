module

public import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits
public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.ComplexSphericalNormalization
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteWhittakerIdentityNeighborhoods

@[expose] public section

noncomputable section
open scoped NumberField Classical
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open NumberField MeasureTheory MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

def tensorFunction (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    Functions R :=
  D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))

theorem core_period_integrable (D : SourceFactorization R Q T)
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad)
    (g : Group R) : Integrable (fun q => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  exact FourierContinuation.sameResidue_period_integrable T (D.core_same_residue x) g

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end

section

noncomputable section
open scoped NumberField Classical
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

def tensorFunction (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    Functions R :=
  D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x))

theorem tensorFunction_update_smul (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (p : s.val) (c : ℂ) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x p (c • x p)) = c • _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x := by
  unfold _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction
  rw [(PiTensorProduct.tprod ℂ).map_update_smul, Function.update_eq_self,
    map_smul, map_smul]

def integrablePeriods : Submodule ℂ (Functions R) where
  carrier := {f | ∀ g, Integrable (fun q => f
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
      star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro f h hf hh g
    convert (hf g).add (hh g) using 1
    ext q
    simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    intro c f hf g
    simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using (hf g).const_mul c

theorem core_period_integrable (D : SourceFactorization R Q T)
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad)
    (g : Group R) : Integrable (fun q => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
        star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq := by
  exact FourierContinuation.sameResidue_period_integrable T (D.core_same_residue x) g

def coreFourier (D : SourceFactorization R Q T) (g : Group R) :
    RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad →ₗ[ℂ] ℂ where
  toFun x := fourier R Q.dq (D.coreMap x) g
  map_add' x y := by
    unfold MomentSources.fourier
    simp only [map_add, Pi.add_apply, add_mul]
    exact integral_add (core_period_integrable R D x g) (core_period_integrable R D y g)
  map_smul' c x := by
    unfold MomentSources.fourier
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem tensorFunction_ne_zero (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (hx : ∀ p, x p ≠ 0) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x ≠ 0 := by
  classical
  let φ : ∀ p : s.val, Module.Dual ℂ (actualLocal R D.finiteData p) := fun p =>
    Classical.choose (Module.Projective.exists_dual_eq_one ℂ (hx p))
  have hφ (p : s.val) : φ p (x p) = 1 :=
    Classical.choose_spec (Module.Projective.exists_dual_eq_one ℂ (hx p))
  let L := PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ φ)
  have hL : L (PiTensorProduct.tprod ℂ x) = 1 := by
    simp [L, PiTensorProduct.dualDistrib_apply, hφ]
  have href (p : KPHilbert.Place F) (hp : p ∉ D.bad) : D.references p ≠ 0 := by
    intro he
    have hv := D.reference_value p hp
    rw [he, map_zero] at hv
    exact zero_ne_one hv
  intro he
  have hcore : RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ x) = 0 :=
    D.core_injective (he.trans (map_zero D.coreMap).symm)
  have ht : PiTensorProduct.tprod ℂ x = 0 :=
    RestrictedTensorSimple.stageInclusion_injective _ D.references D.bad href s
      (hcore.trans (map_zero _).symm)
  rw [ht, map_zero] at hL
  exact zero_ne_one hL

theorem spherical_frozen_tensor (D : SourceFactorization R Q T) :
    ∃ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ p : s.val, actualLocal R D.finiteData p),
      s.val = D.bad ∧
      (∀ (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val),
        x ⟨Sum.inl w, hw⟩ = sphericalCoreSeed) ∧
      (∀ (q : R.A.Sf) (hq : Sum.inr q.val ∈ s.val),
        D.ell (Sum.inr q.val) (x ⟨Sum.inr q.val, hq⟩) = 1) ∧
      (∀ g, Integrable (fun q => tensorFunction R D s x
        (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) *
          star (adelicTraceQuotientCharacter F q : ℂ)) Q.dq) ∧
      tensorFunction R D s x ∈ sameResidueModule T ∧
      fourier R Q.dq (tensorFunction R D s x) 1 =
        ∏ p : s.val, D.ell p (x p) ∧ tensorFunction R D s x ≠ 0 := by
  choose v V hv hVo hV1 hV using factorization_finite_unit_vector R D
  let s : RestrictedTensorSimple.Level D.bad := ⟨D.bad, le_rfl⟩
  let x : ∀ p : s.val, actualLocal R D.finiteData p := fun p =>
    match p.val with
    | Sum.inl _ => sphericalCoreSeed
    | Sum.inr q => if hq : q ∈ R.A.Sf then v ⟨q, hq⟩ else D.references (Sum.inr q)
  refine ⟨s, x, rfl, ?_, ?_, ?_, D.core_same_residue _, D.product_exact s x, ?_⟩
  · intro w hw
    rfl
  · intro q hq
    change D.ell (Sum.inr q.val)
      (if h : q.val ∈ R.A.Sf then v ⟨q.val, h⟩ else D.references (Sum.inr q.val)) = 1
    rw [dif_pos q.property]
    exact hv q
  · intro g
    exact core_period_integrable R D _ g
  · apply tensorFunction_ne_zero R D s x
    intro p
    rcases p with ⟨p, hp⟩
    cases p with
    | inl w => exact sphericalCoreSeed_ne_zero
    | inr q =>
      have hq : q ∈ R.A.Sf := by
        have hb := (D.bad_exact (Sum.inr q)).mp hp
        rcases hb with ⟨w, hw⟩ | ⟨q', he, hq'⟩
        · cases hw
        · cases he
          exact hq'
      change (if h : q ∈ R.A.Sf then v ⟨q, h⟩ else D.references (Sum.inr q)) ≠ 0
      rw [dif_pos hq]
      intro hz
      have hh := hv ⟨q, hq⟩
      rw [hz, map_zero] at hh
      exact zero_ne_one hh

theorem tensorFunction_spherical_compact (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val)
    (hx : x ⟨Sum.inl w, hw⟩ = sphericalCoreSeed)
    (k : KPCplxCharacterHaar.ComplexSU2) (g : Group R) :
    _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k) =
        _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s x g := by
  have hi := D.complex_intertwining w k s hw x g
  change _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.tensorFunction R D s (Function.update x ⟨Sum.inl w, hw⟩
    (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))) g = _ at hi
  have hfix : KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩) =
      x ⟨Sum.inl w, hw⟩ := by rw [hx, sphericalCoreSeed_SU2_fixed]
  rw [hfix, Function.update_eq_self] at hi
  exact hi.symm

end DedekindZetaZeroFree.RootDerivatives

end
end
