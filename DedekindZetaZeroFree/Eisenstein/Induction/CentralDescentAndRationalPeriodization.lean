module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.RestrictedTensorVectors

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem localValue_scalar (p : KPHilbert.Place F) (f : Plus R N P C p)
    (z : (KPHilbert.Completion F p)ˣ)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) :
    localValue R N P C p (KPScalarSplitCentral.scalarHom F R.A.zeta12
      R.A.primitive_zeta12 p z * g) f = localValue R N P C p g f := by
  cases p with
  | inr q =>
    change f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr q) (_ * _)) = _
    rw [map_mul]
    have hs : KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (KPScalarSplitCentral.scalarHom F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
    rw [hs, one_mul]
    rfl
  | inl w =>
    have he : (KPScalarSplitCentral.scalarHom F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) z * g).epsilon = g.epsilon := by
      change 1 * g.epsilon * KPLocalCover.sigmaTwo F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) _ _ = _
      rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
      simp
    have hm : complexMatrix R w (KPScalarSplitCentral.scalarHom F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inl w) z * g) =
        Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)).toRingHom z) *
          complexMatrix R w g := by
      unfold complexMatrix
      change Matrix.GeneralLinearGroup.map _ (_ * g.g) = _
      rw [map_mul]
      congr 1
      apply Units.ext
      ext i j
      simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
        KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.GeneralLinearGroup.map,
        Matrix.diagonal, Pi.algebraMap_def]
      split_ifs <;> simp
    change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
      R.A.primitive_zeta12 _ : ℂ) * f.val _ = _
    rw [he, hm, KPCplxPrincipalSeriesCharts.central_invariance]
    rfl

theorem rawCoreVector_scalar (x : PlusCore R N P C)
    (z : KPAdelicCoverRestrictedProduct.Ideles F) (g : Raw R) :
    rawCoreVector R N P C (KPAdelicCoverRestrictedProduct.scalarTuple F R.A.zeta12
      R.A.primitive_zeta12 z * g) x = rawCoreVector R N P C g x := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, y, rfl⟩ := Module.DirectLimit.exists_of x
  apply rawCoreVector_congr
  intro p f
  exact localValue_scalar R N P C p f (Units.map (KPAdelicCoverRestrictedProduct.adeleEval F p) z) (g p)

theorem localValue_central (p : KPHilbert.Place F) (f : Plus R N P C p)
    (e : rootsOfUnity 3 F)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) :
    localValue R N P C p (KPLocalCover.centralInjection F R.A.zeta12
      R.A.primitive_zeta12 p e * g) f =
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 e : ℂ) • localValue R N P C p g f := by
  cases p with
  | inl w =>
    change (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
      R.A.primitive_zeta12 _ : ℂ) * f.val _ = _
    have he : (KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) e * g).epsilon = e * g.epsilon := by
      change e * g.epsilon * KPLocalCover.sigmaTwo F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inl w) 1 g.g = _
      rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
    have hm : complexMatrix R w (KPLocalCover.centralInjection F R.A.zeta12
        R.A.primitive_zeta12 (Sum.inl w) e * g) = complexMatrix R w g := by
      unfold complexMatrix
      congr 1
      exact one_mul g.g
    rw [he, hm, map_mul, Units.val_mul]
    exact mul_assoc _ _ _
  | inr q =>
    let T := (imageData R N P C q).inducing
    let B := T.openCell T.polarization
    have hv := f.property.1 (T.borel.torus (B.centralTorus e))
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) g)
    have hs : KPLocalPrincipalSeries.inducingScalar T.borel 0
        (T.borel.torus (B.centralTorus e)) = 1 := by
      simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.deltaHalf,
        KPLocalPrincipalSeries.normPower, T.borel.retract_torus, B.central_coordinate,
        KPLocalPrincipalSeries.localAbs_one]
    change f.val (_ * _) = _ at hv
    rw [B.central_eq] at hv
    change f.val _ = KPLocalPrincipalSeries.inducingScalar T.borel 0
      (T.borel.torus (B.centralTorus e)) •
        KPLocalPrincipalSeries.borelAction T.borel T.polarization .plus
          (T.borel.torus (B.centralTorus e)) (f.val _) at hv
    rw [hs, one_smul, B.genuine] at hv
    change f.val (KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (_ * _)) = _
    rw [map_mul]
    have heta : B.eta = KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
        R.A.primitive_zeta12 := T.openCell_ordinary T.polarization
    rw [heta] at hv
    exact hv

theorem rawCoreVector_centralTuple (x : PlusCore R N P C)
    (e : KPAdelicCoverRestrictedProduct.CentralTuples F) (g : Raw R) :
    rawCoreVector R N P C (KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12
      R.A.primitive_zeta12 e * g) x =
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.centralProduct F e) : ℂ) • rawCoreVector R N P C g x := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, y, rfl⟩ := Module.DirectLimit.exists_of x
  obtain ⟨u, hu⟩ := exists_reference_stage R N P C g
  let t : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨s.val ∪ u.val ∪ (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F e).toFinset,
      (s.property.trans Finset.subset_union_left).trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left.trans Finset.subset_union_left
  have he : ∀ p, p ∉ t.val → e p = 1 := by
    intro p hp
    by_contra h
    exact hp (Finset.mem_union_right _
      ((KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F e).mem_toFinset.mpr h))
  have ht : ∀ p, p ∉ t.val → localValue R N P C p (g p)
      (plusReference R N P C p) = reference R P C p :=
    fun p hp => hu p (fun h => hp (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have ht' : ∀ p, p ∉ t.val → localValue R N P C p
      ((KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e * g) p)
      (plusReference R N P C p) = reference R P C p := by
    intro p hp
    change localValue R N P C p (KPLocalCover.centralInjection F R.A.zeta12
      R.A.primitive_zeta12 p (e p) * g p) _ = _
    rw [localValue_central, he p hp, map_one, Units.val_one, one_smul]
    exact ht p hp
  let z := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s t hst y
  have hins : RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C)
      (bad R P C) t z = RestrictedTensorSimple.stageInclusion (Plus R N P C)
        (plusReference R N P C) (bad R P C) s y := Module.DirectLimit.of_f
  change rawCoreVector R N P C _ (RestrictedTensorSimple.stageInclusion
    (Plus R N P C) (plusReference R N P C) (bad R P C) s y) =
      _ • rawCoreVector R N P C g (RestrictedTensorSimple.stageInclusion
        (Plus R N P C) (plusReference R N P C) (bad R P C) s y)
  rw [← hins, rawCoreVector_stage R N P C t _ ht', rawCoreVector_stage R N P C t g ht]
  have hp : (∏ p : t.val, (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
      R.A.primitive_zeta12 (e p) : ℂ)) =
      (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.centralProduct F e) : ℂ) := by
    change _ = ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
      R.A.primitive_zeta12) (∏ᶠ p, e p) : ℂ)
    rw [finprod_eq_prod_of_mulSupport_subset _ (fun p hp => by
      by_contra h
      exact hp (he p h))]
    rw [map_prod]
    exact (Finset.prod_coe_sort t.val (fun p => (KPSourceConvention.ordinaryGenuineCharacter
      F R.A.zeta12 R.A.primitive_zeta12 (e p) : ℂ))).trans
      (map_prod (Units.coeHom ℂ) (fun p => KPSourceConvention.ordinaryGenuineCharacter
        F R.A.zeta12 R.A.primitive_zeta12 (e p)) t.val).symm
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c z =>
    simp only [map_smul]
    rw [stageVector_pure, stageVector_pure]
    have hv : (fun p : t.val => localValue R N P C p
        ((KPAdelicCoverRestrictedProduct.centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 e * g) p)
        (z p)) = (fun p : t.val => (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
          R.A.primitive_zeta12 (e p) : ℂ) • localValue R N P C p (g p) (z p)) := by
      funext p
      exact localValue_central R N P C p (z p) (e p) (g p)
    rw [hv, MultilinearMap.map_smul_univ, hp, map_smul]
    exact smul_comm _ _ _
  | add z w hz hw => simp only [map_add, hz, hw, smul_add]

theorem rawCoreVector_amalgamation_invariant (x : PlusCore R N P C)
    (m : KPAdelicCoverRestrictedProduct.M F R.A.zeta12 R.A.primitive_zeta12) (g : Raw R) :
    rawCoreVector R N P C (m.val * g) x = rawCoreVector R N P C g x := by
  obtain ⟨e, he, hm⟩ := Subgroup.mem_map.mp m.property
  change KPAdelicCoverRestrictedProduct.centralProduct F e = 1 at he
  rw [← hm, rawCoreVector_centralTuple, he, map_one, Units.val_one, one_smul]

local notation "GL" => KPAdelicCoverRestrictedProduct.CubicGL2Adelic F R.A.zeta12 R.A.primitive_zeta12

 theorem rawCoreVector_amalgamation_eq (x : PlusCore R N P C) (g h : Raw R)
    (he : KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g =
      KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 h) :
    rawCoreVector R N P C g x = rawCoreVector R N P C h x := by
  have hm : g⁻¹ * h ∈ KPAdelicCoverRestrictedProduct.M F R.A.zeta12 R.A.primitive_zeta12 :=
    QuotientGroup.eq.mp he
  have hc := KPAdelicCoverRestrictedProduct.M_central F R.A.zeta12 R.A.primitive_zeta12 hm
  have hh : (⟨g⁻¹ * h, hm⟩ : KPAdelicCoverRestrictedProduct.M
      F R.A.zeta12 R.A.primitive_zeta12).val * g = h := by
    change (g⁻¹ * h) * g = h
    rw [← Subgroup.mem_center_iff.mp hc g, ← mul_assoc, mul_inv_cancel, one_mul]
  have hi := rawCoreVector_amalgamation_invariant R N P C x ⟨_, hm⟩ g
  rw [hh] at hi
  exact hi.symm

def amalgamatedCoreVector (x : PlusCore R N P C) : GL → FiberCore R P C :=
  Quotient.lift (fun g : Raw R => rawCoreVector R N P C g x)
    (fun g h he => rawCoreVector_amalgamation_eq R N P C x g h (Quotient.sound he))

@[simp] theorem amalgamatedCoreVector_raw (x : PlusCore R N P C) (g : Raw R) :
    amalgamatedCoreVector R N P C x
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g) =
      rawCoreVector R N P C g x := rfl

theorem amalgamatedCoreVector_scalar (x : PlusCore R N P C)
    (z : KPAdelicCoverRestrictedProduct.Ideles F) (g : GL) :
    amalgamatedCoreVector R N P C x (KPAdelicCoverRestrictedProduct.scalarHom F R.A.zeta12
      R.A.primitive_zeta12 z * g) = amalgamatedCoreVector R N P C x g := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change amalgamatedCoreVector R N P C x
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.scalarTuple F R.A.zeta12 R.A.primitive_zeta12 z) *
        KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g) = _
    rw [← map_mul, amalgamatedCoreVector_raw]
    change _ = rawCoreVector R N P C g x
    exact rawCoreVector_scalar R N P C x z g

 theorem amalgamatedCoreVector_quotient_eq (x : PlusCore R N P C) (g h : GL)
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 g =
      KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12 h) :
    amalgamatedCoreVector R N P C x g = amalgamatedCoreVector R N P C x h := by
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp he
  have hc := KPAdelicCoverRestrictedProduct.scalarHom_central F R.A.zeta12
    R.A.primitive_zeta12 (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hh : KPAdelicCoverRestrictedProduct.scalarHom F R.A.zeta12
      R.A.primitive_zeta12 z * g = h := by
    rw [← Subgroup.mem_center_iff.mp hc g, hz, ← mul_assoc, mul_inv_cancel, one_mul]
  have hi := amalgamatedCoreVector_scalar R N P C x z g
  rw [hh] at hi
  exact hi.symm

def quotientCoreVector (x : PlusCore R N P C) : Group R → FiberCore R P C :=
  Quotient.lift (fun g : GL => amalgamatedCoreVector R N P C x g)
    (fun g h he => amalgamatedCoreVector_quotient_eq R N P C x g h (Quotient.sound he))

@[simp] theorem quotientCoreVector_raw (x : PlusCore R N P C) (g : Raw R) :
    quotientCoreVector R N P C x (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12
      R.A.primitive_zeta12 (KPAdelicCoverRestrictedProduct.amalgamation
        F R.A.zeta12 R.A.primitive_zeta12 g)) = rawCoreVector R N P C g x := rfl

def quotientCoreEvaluator : PlusCore R N P C →ₗ[ℂ] (Group R → FiberCore R P C) where
  toFun := quotientCoreVector R N P C
  map_add' x y := by
    funext g
    induction g using QuotientGroup.induction_on with
    | H g =>
      induction g using QuotientGroup.induction_on with
      | H g => exact map_add (rawCoreVector R N P C g) x y
  map_smul' c x := by
    funext g
    induction g using QuotientGroup.induction_on with
    | H g =>
      induction g using QuotientGroup.induction_on with
      | H g => exact map_smul (rawCoreVector R N P C g) c x

def quotientRationalEvaluator : PlusCore R N P C →ₗ[ℂ]
    (Group R → KPGlobalResidualConstruction.smoothRationalFiber
      F R.A.zeta12 R.A.primitive_zeta12) where
  toFun x g := comparisonSmooth R P C (quotientCoreVector R N P C x g)
  map_add' x y := by
    funext g
    rw [show quotientCoreVector R N P C (x + y) g =
      quotientCoreVector R N P C x g + quotientCoreVector R N P C y g from
        congrFun ((quotientCoreEvaluator R N P C).map_add x y) g, map_add]
    rfl
  map_smul' c x := by
    funext g
    rw [show quotientCoreVector R N P C (c • x) g = c • quotientCoreVector R N P C x g from
      congrFun ((quotientCoreEvaluator R N P C).map_smul c x) g, map_smul]
    rfl

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
