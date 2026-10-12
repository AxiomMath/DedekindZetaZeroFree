module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexPrincipalSeries.TopologicalImage
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactness
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.CentralDescent
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarmonicTensorFiniteness

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPGlobalTorusFiniteStages KPLocalPrincipalSeries
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

local instance rawTopology (q : KPFinitePlace F) :
    TopologicalSpace (KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :=
  KPAdelicCoverRestrictedProduct.localTopology F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)

def finiteMaxAction (q : KPFinitePlace F) :
    Representation ℂ (ThetaExpansion.iwasawaCompactFactor R (Sum.inr q))
      (Plus R.A P C (Sum.inr q)) :=
  (IPlus (C.canonical q).borel (C.polarization q)).comp
    ((KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)).comp
      (ThetaExpansion.iwasawaCompactFactor R (Sum.inr q)).subtype)

def finiteMaxOrbit (q : KPFinitePlace F) (f : Plus R.A P C (Sum.inr q)) :
    Submodule ℂ (Plus R.A P C (Sum.inr q)) :=
  Submodule.span ℂ (Set.range (fun k => finiteMaxAction R P C q k f))

theorem finiteMaxOrbit_finite (q : KPFinitePlace F) (f : Plus R.A P C (Sum.inr q)) :
    Module.Finite ℂ (finiteMaxOrbit R P C q f) := by
  let : CompactSpace (ThetaExpansion.iwasawaCompactFactor R (Sum.inr q)) :=
    isCompact_iff_compactSpace.mp (ThetaExpansion.iwasawa_compact_factor_is_compact R (Sum.inr q))
  apply Module.Finite.span_of_finite
  have h := KPLocalInducedCompactPairing.smooth_orbit_locallyConstant
    (IPlus (C.canonical q).borel (C.polarization q)) f
    (principalSeries_smooth (C.canonical q).borel (C.polarization q) .plus 0 f)
  have hq : Continuous (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :=
    QuotientGroup.continuous_mk
  exact (h.comp_continuous (hq.comp continuous_subtype_val)).range_finite

theorem mem_finiteMaxOrbit (q : KPFinitePlace F) (f : Plus R.A P C (Sum.inr q)) :
    f ∈ finiteMaxOrbit R P C q f := by
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  change finiteMaxAction R P C q 1 f = f
  rw [map_one]
  rfl

theorem finiteMaxOrbit_stable (q : KPFinitePlace F) (f : Plus R.A P C (Sum.inr q))
    (k : ThetaExpansion.iwasawaCompactFactor R (Sum.inr q)) :
    ∀ x ∈ finiteMaxOrbit R P C q f, finiteMaxAction R P C q k x ∈ finiteMaxOrbit R P C q f := by
  apply Submodule.span_induction
  · rintro x ⟨j, rfl⟩
    rw [← Module.End.mul_apply, ← map_mul]
    exact Submodule.subset_span ⟨k * j, rfl⟩
  · simp
  · intro x y hx hy hix hiy
    simpa only [map_add] using Submodule.add_mem _ hix hiy
  · intro c x hx hix
    simpa only [map_smul] using Submodule.smul_mem _ c hix

theorem finiteMaxAction_value (q : KPFinitePlace F)
    (k : ThetaExpansion.iwasawaCompactFactor R (Sum.inr q))
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (f : Plus R.A P C (Sum.inr q)) :
    localValue R.A P C (Sum.inr q) g (finiteMaxAction R P C q k f) =
      localValue R.A P C (Sum.inr q) (g * k.val) f := by
  change f.val (_ * _) = f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) (g * k.val))
  rw [map_mul]
  rfl

theorem finiteMax_reference (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (hbad : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (k : ThetaExpansion.iwasawaCompactFactor R (Sum.inr q)) :
    finiteMaxAction R P C q k (plusReference R.A P C (Sum.inr q)) =
      plusReference R.A P C (Sum.inr q) := by
  have hk := k.property
  change k.val ∈ (if KPAdelicCoverRestrictedProduct.Bad F q then _
    else KPAdelicCoverRestrictedProduct.finiteCompact F R.A.zeta12 R.A.primitive_zeta12 q) at hk
  rw [if_neg hbad, KPAdelicCoverRestrictedProduct.finiteCompact, dite_eq_right hbad] at hk
  obtain ⟨l, hl⟩ := hk
  have hmem : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k.val ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    have hm : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k.val ∈
        (KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12 R.A.primitive_zeta12 q
          (C.actual_compact q hq).choose).range := by
      refine ⟨l, ?_⟩
      change KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 q _ l) = _
      rw [hl]
    exact Eq.mpr (congrArg (fun K : Subgroup
      (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) =>
        KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) k.val ∈ K)
          (C.actual_compact q hq).choose_spec) hm
  exact plusReference_fixed R.A P C q hq ⟨_, hmem⟩

open KPCplxPrincipalSeriesCharts KPReferenceChange.StandardComplexImage

theorem archMax_matrix (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))
    (hg : g ∈ ThetaExpansion.iwasawaCompactFactor R (Sum.inl w)) :
    rawMatrix R.A w g ∈ compactSubgroup := by
  apply (show ThetaExpansion.complexSU2Compact R w ≤
    compactSubgroup.comap (rawMatrix R.A w) from ?_) hg
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨k, rfl⟩
  change rawMatrix R.A w _ ∈
    (Matrix.ProjGenLinGroup.mk.comp KPCplxCharacterHaar.complexSU2Embedding).range
  apply MonoidHom.mem_range.mpr
  refine ⟨k, ?_⟩
  change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding k) =
    Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (coordinate R.A w).toRingHom
      (Matrix.GeneralLinearGroup.map (coordinate R.A w).symm.toRingHom
        (KPCplxCharacterHaar.complexSU2Embedding k)))
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (RingEquiv.apply_symm_apply (coordinate R.A w) _).symm

def archMaxAction (w : InfinitePlace F)
    (k : ThetaExpansion.iwasawaCompactFactor R (Sum.inl w)) :
    Plus R.A P C (Sum.inl w) →ₗ[ℂ] Plus R.A P C (Sum.inl w) :=
  (rawCentralCharacter R.A w k.val : ℂ) • KPLiteralScalarArchTensor.compactAction
    ⟨rawMatrix R.A w k.val, archMax_matrix R w k.val k.property⟩

theorem archMax_finite_subspace (w : InfinitePlace F) (f : Plus R.A P C (Sum.inl w)) :
    ∃ U : Submodule ℂ (Plus R.A P C (Sum.inl w)),
      Module.Finite ℂ U ∧ f ∈ U ∧
        ∀ k x, x ∈ U → archMaxAction R P C w k x ∈ U := by
  obtain ⟨U, hU, hf, hinv⟩ := KPLiteralScalarArchTensor.finite_local_subspace f
  exact ⟨U, hU, hf, fun k x hx => U.smul_mem _ (hinv _ x hx)⟩

theorem archMaxAction_value (w : InfinitePlace F)
    (k : ThetaExpansion.iwasawaCompactFactor R (Sum.inl w))
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))
    (f : Plus R.A P C (Sum.inl w)) :
    localValue R.A P C (Sum.inl w) g (archMaxAction R P C w k f) =
      localValue R.A P C (Sum.inl w) (g * k.val) f := by
  change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 g.epsilon : ℂ) *
    ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 k.val.epsilon : ℂ) *
      f.val (complexMatrix R.A w g * complexMatrix R.A w k.val)) =
    (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12 (g * k.val).epsilon : ℂ) *
      f.val (complexMatrix R.A w (g * k.val))
  have he : (g * k.val).epsilon = g.epsilon * k.val.epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
  have hm : complexMatrix R.A w (g * k.val) = complexMatrix R.A w g * complexMatrix R.A w k.val := map_mul _ _ _
  rw [he, hm, map_mul, Units.val_mul, mul_assoc]

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
