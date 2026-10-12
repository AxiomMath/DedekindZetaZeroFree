module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RestrictedTensorProduct

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPGlobalTorusFiniteStages KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Places" => KPHilbert.Place

theorem localValue_scalar (v : Places F) (f : Plus A P C v)
 (z : (KPHilbert.Completion F v)ˣ)
 (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
 localValue A P C v (KPScalarSplitCentral.scalarHom F ζ hζ v z * g) f = localValue A P C v g f := by
 cases v with
 | inr q =>
   change f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (_ * _)) = _
   rw [map_mul]
   have hs : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
     (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z) = 1 :=
     (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨z,rfl⟩)
   rw [hs, one_mul]
   rfl
 | inl w =>
   have he : (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g).epsilon = g.epsilon := by
     change 1 * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
     rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
     simp
   have hm : complexMatrix A w (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inl w) z * g) =
     Matrix.GeneralLinearGroup.scalar (Fin 2)
       (Units.map (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
         (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom z) * complexMatrix A w g := by
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
   change (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ _ : ℂ) * f.val _ = _
   rw [he, hm, KPCplxPrincipalSeriesCharts.central_invariance]
   rfl

theorem rawCoreInsertion_congr (g h : Raw A)
    (hlocal : ∀ v f, localValue A P C v (g v) f = localValue A P C v (h v) f)
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    rawCoreInsertion A P C x g = rawCoreInsertion A P C x h := by
  let : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    obtain ⟨u, hu⟩ := exists_reference_stage A P C g
    let t : RestrictedTensorSimple.Level (bad A P C) := ⟨s.val ∪ u.val,
      s.property.trans Finset.subset_union_left⟩
    have hst : s ≤ t := Finset.subset_union_left
    have htail : ∀ v, v ∉ t.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v :=
      fun v hv => hu v (fun hvu => hv (Finset.mem_union_right _ hvu))
    have htail' : ∀ v, v ∉ t.val → localValue A P C v (h v) (plusReference A P C v) = reference A P C v :=
      fun v hv => (hlocal v _).symm.trans (htail v hv)
    have heq : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
        (bad A P C) s x = RestrictedTensorSimple.stageInclusion (Plus A P C)
        (plusReference A P C) (bad A P C) t
        (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t hst x) :=
      Module.DirectLimit.of_f.symm
    change rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) g =
      rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) h
    rw [heq, rawCoreInsertion_stage A P C t _ g htail,
      rawCoreInsertion_stage A P C t _ h htail']
    have hm : (fun j : t.val => localValueMap A P C j.val (g j.val)) =
        (fun j : t.val => localValueMap A P C j.val (h j.val)) := by
      funext j
      ext f
      exact hlocal j.val f
    simp only [rawStageValue, LinearMap.comp_apply, hm]

theorem rawCoreInsertion_scalar (z : KPAdelicCoverRestrictedProduct.Ideles F)
    (g : Raw A) (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    rawCoreInsertion A P C x (KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ z * g) =
      rawCoreInsertion A P C x g := by
  apply rawCoreInsertion_congr
  intro v f
  exact localValue_scalar A P C v f _ (g v)

theorem localValue_central (v : Places F) (f : Plus A P C v) (e : rootsOfUnity 3 F)
 (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
 localValue A P C v (KPLocalCover.centralInjection F ζ hζ v e * g) f =
   (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ e : ℂ) • localValue A P C v g f := by
 cases v with
 | inl w =>
   change (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ _ : ℂ) * f.val _ = _
   have he : (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g).epsilon = e * g.epsilon := by
     change e * g.epsilon * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) 1 g.g = _
     rw [KPLocalChartTopology.complex_sigmaTwo_eq_one, mul_one]
   have hm : complexMatrix A w (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) e * g) =
     complexMatrix A w g := by
     unfold complexMatrix
     congr 1
     exact one_mul g.g
   rw [he, hm, map_mul, Units.val_mul]
   exact mul_assoc _ _ _
 | inr q =>
   let S := C.canonical q
   let B := S.openCell (C.polarization q)
   have hv := f.property.1 (S.borel.torus (B.centralTorus e))
     (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g)
   have hs : KPLocalPrincipalSeries.inducingScalar S.borel 0
     (S.borel.torus (B.centralTorus e)) = 1 := by
     simp [KPLocalPrincipalSeries.inducingScalar, KPLocalPrincipalSeries.deltaHalf,
       KPLocalPrincipalSeries.normPower, S.borel.retract_torus, B.central_coordinate,
       KPLocalPrincipalSeries.localAbs_one]
   change f.val (_ * _) = _ at hv
   rw [B.central_eq] at hv
   change f.val _ = KPLocalPrincipalSeries.inducingScalar S.borel 0
     (S.borel.torus (B.centralTorus e)) •
       KPLocalPrincipalSeries.borelAction S.borel (C.polarization q) .plus
         (S.borel.torus (B.centralTorus e)) (f.val _) at hv
   rw [hs, one_smul, B.genuine] at hv
   change f.val (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (_ * _)) = _
   rw [map_mul]
   have heta : B.eta = KPSourceConvention.ordinaryGenuineCharacter F ζ hζ := S.openCell_ordinary (C.polarization q)
   rw [heta] at hv
   exact hv

theorem rawStageValue_centralTuple (s : RestrictedTensorSimple.Level (bad A P C))
    (e : KPAdelicCoverRestrictedProduct.CentralTuples F) (g : Raw A)
    (x : RestrictedTensorSimple.Stage (Plus A P C) s.val) :
    rawStageValue A P C s (KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ e * g) x =
      (∏ j : s.val, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e j.val) : ℂ)) *
        rawStageValue A P C s g x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul, smul_eq_mul]
    rw [← mul_left_comm c]
    congr 1
    unfold rawStageValue
    simp only [LinearMap.comp_apply, PiTensorProduct.map_tprod]
    change (rationalEvaluation A) (comparison A P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ
        (fun j => localValue A P C j.val
          (KPLocalCover.centralInjection F ζ hζ j.val (e j.val) * g j.val) (x j))))) = _
    simp_rw [localValue_central]
    rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
    simp only [map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

theorem rawCoreInsertion_centralTuple
    (e : KPAdelicCoverRestrictedProduct.CentralTuples F) (g : Raw A)
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)) :
    rawCoreInsertion A P C x (KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ e * g) =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ
        (KPAdelicCoverRestrictedProduct.centralProduct F e) : ℂ) * rawCoreInsertion A P C x g := by
  let : Nonempty (RestrictedTensorSimple.Level (bad A P C)) := ⟨⟨bad A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    obtain ⟨u, hu⟩ := exists_reference_stage A P C g
    let E := (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F e).toFinset
    let t : RestrictedTensorSimple.Level (bad A P C) := ⟨s.val ∪ u.val ∪ E,
      (s.property.trans Finset.subset_union_left).trans Finset.subset_union_left⟩
    have hst : s ≤ t := Finset.subset_union_left.trans Finset.subset_union_left
    have he : ∀ v, v ∉ t.val → e v = 1 := by
      intro v hv
      by_contra hn
      exact hv (Finset.mem_union_right _ (Set.Finite.mem_toFinset _ |>.mpr hn))
    have ht : ∀ v, v ∉ t.val → localValue A P C v (g v) (plusReference A P C v) = reference A P C v :=
      fun v hv => hu v (fun hvu => hv (Finset.mem_union_left _ (Finset.mem_union_right _ hvu)))
    have ht' : ∀ v, v ∉ t.val → localValue A P C v
        ((KPAdelicCoverRestrictedProduct.centralTupleMap F ζ hζ e * g) v)
        (plusReference A P C v) = reference A P C v := by
      intro v hv
      change localValue A P C v (KPLocalCover.centralInjection F ζ hζ v (e v) * g v) _ = _
      rw [localValue_central, he v hv, map_one, Units.val_one, one_smul]
      exact ht v hv
    have heq : RestrictedTensorSimple.stageInclusion (Plus A P C) (plusReference A P C)
        (bad A P C) s x = RestrictedTensorSimple.stageInclusion (Plus A P C)
        (plusReference A P C) (bad A P C) t
        (RestrictedTensorSimple.transition (Plus A P C) (plusReference A P C) (bad A P C) s t hst x) :=
      Module.DirectLimit.of_f.symm
    change rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) _ =
      _ * rawCoreInsertion A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x) g
    rw [heq, rawCoreInsertion_stage A P C t _ _ ht', rawCoreInsertion_stage A P C t _ g ht,
      rawStageValue_centralTuple]
    congr 1
    change _ = ((KPSourceConvention.ordinaryGenuineCharacter F ζ hζ) (∏ᶠ v, e v) : ℂ)
    rw [finprod_eq_prod_of_mulSupport_subset _ (fun v hv => by
      by_contra hn
      exact hv (he v hn))]
    rw [map_prod]
    exact (Finset.prod_coe_sort t.val (fun v => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e v) : ℂ))).trans
      (map_prod (Units.coeHom ℂ) (fun v => KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e v)) t.val).symm

theorem rawCoreValue_amalgamation_invariant
 (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
 (m : KPAdelicCoverRestrictedProduct.M F ζ hζ) (g : Raw A) :
 rawCoreValue A P C (m.val * g) x = rawCoreValue A P C g x := by
 obtain ⟨e, he, hm⟩ := Subgroup.mem_map.mp m.property
 change KPAdelicCoverRestrictedProduct.centralProduct F e = 1 at he
 change rawCoreInsertion A P C x _ = rawCoreInsertion A P C x g
 rw [← hm, rawCoreInsertion_centralTuple, he, map_one, Units.val_one, one_mul]

set_option quotPrecheck false
local notation "Core" => RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C)
local notation "GL" => KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ
theorem rawCoreValue_amalgamation_eq (x : Core) (g h : Raw A)
 (he : KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ g =
   KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ h) :
 rawCoreValue A P C g x = rawCoreValue A P C h x := by
 have hm : g⁻¹ * h ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := QuotientGroup.eq.mp he
 have hc := KPAdelicCoverRestrictedProduct.M_central F ζ hζ hm
 have hh : (⟨g⁻¹ * h, hm⟩ : KPAdelicCoverRestrictedProduct.M F ζ hζ).val * g = h := by
   change (g⁻¹ * h) * g = h
   rw [← Subgroup.mem_center_iff.mp hc g, ← mul_assoc, mul_inv_cancel, one_mul]
 have hi := rawCoreValue_amalgamation_invariant A P C x ⟨_,hm⟩ g
 rw [hh] at hi
 exact hi.symm

def amalgamatedCoreValue (x : Core) : GL → ℂ :=
 Quotient.lift (fun g : Raw A => rawCoreValue A P C g x)
   (fun g h he => rawCoreValue_amalgamation_eq A P C x g h (Quotient.sound he))
@[simp] theorem amalgamatedCoreValue_raw (x : Core) (g : Raw A) :
 amalgamatedCoreValue A P C x (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ g) =
 rawCoreValue A P C g x := rfl

theorem amalgamatedCoreValue_scalar (x : Core)
 (z : KPAdelicCoverRestrictedProduct.Ideles F) (g : GL) :
 amalgamatedCoreValue A P C x (KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ z * g) =
 amalgamatedCoreValue A P C x g := by
 induction g using QuotientGroup.induction_on with
 | H g =>
   change amalgamatedCoreValue A P C x
     (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ z) *
       KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ g) = _
   rw [← map_mul, amalgamatedCoreValue_raw]
   change _ = rawCoreValue A P C g x
   exact rawCoreInsertion_scalar A P C z g x

theorem amalgamatedCoreValue_quotient_eq (x : Core) (g h : GL)
 (he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ g =
   KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ h) :
 amalgamatedCoreValue A P C x g = amalgamatedCoreValue A P C x h := by
 obtain ⟨z, hz⟩ := QuotientGroup.eq.mp he
 have hc := KPAdelicCoverRestrictedProduct.scalarHom_central F ζ hζ (MonoidHom.mem_range.mpr ⟨z,rfl⟩)
 have hh : KPAdelicCoverRestrictedProduct.scalarHom F ζ hζ z * g = h := by
   rw [← Subgroup.mem_center_iff.mp hc g, hz, ← mul_assoc, mul_inv_cancel, one_mul]
 have hi := amalgamatedCoreValue_scalar A P C x z g
 rw [hh] at hi
 exact hi.symm

def quotientCoreValue (x : Core) : G F ζ hζ → ℂ :=
 Quotient.lift (fun g : GL => amalgamatedCoreValue A P C x g)
   (fun g h he => amalgamatedCoreValue_quotient_eq A P C x g h (Quotient.sound he))
@[simp] theorem quotientCoreValue_raw (x : Core) (g : Raw A) :
 quotientCoreValue A P C x (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
   (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ g)) = rawCoreValue A P C g x := rfl

def quotientCoreEvaluator : Core →ₗ[ℂ] (G F ζ hζ → ℂ) where
 toFun := quotientCoreValue A P C
 map_add' x y := by
   funext g
   induction g using QuotientGroup.induction_on with
   | H g =>
     induction g using QuotientGroup.induction_on with
     | H g => exact map_add (rawCoreValue A P C g) x y
 map_smul' c x := by
   funext g
   induction g using QuotientGroup.induction_on with
   | H g =>
     induction g using QuotientGroup.induction_on with
     | H g => exact map_smul (rawCoreValue A P C g) c x

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
