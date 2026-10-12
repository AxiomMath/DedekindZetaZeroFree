module

public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarSections.FlatInsertion
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HarmonicQuotient.LieEquivariance
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorEvaluation.MatrixExponentialDerivatives
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.TensorWords.CyclicSlotDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct Topology
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open HCGeneration
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

def stageLieSlot (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (b : Fin 6) :
    Module.End ℂ (RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :=
  tensorSlot ⟨Sum.inl w, hw⟩ (harmonicPlusDerivative b)

theorem localValue_basis_hasDerivAt (w : InfinitePlace F) (b : Fin 6)
    (f : Plus R.A P C (.inl w))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (.inl w)) :
    HasDerivAt (fun t : ℝ => localValue R.A P C (.inl w)
      (g * rawBasisExponential R w b t) f)
      (localValue R.A P C (.inl w) g (harmonicPlusDerivative b f)) 0 := by
  have he (t : ℝ) : localValue R.A P C (.inl w) (g * rawBasisExponential R w b t) f =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ g.epsilon : ℂ) *
      f.val (complexMatrix R.A w g * KPSmoothActualFlowData.matrixExponential
        ((t : ℂ) • KPSmoothActualFlowData.basisMatrix b)) := by
    have h := rawBasisExponential_local R w b t g
    change (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ _ : ℂ) * f.val _ = _
    rw [h.1]
    exact congrArg (_ * ·) (congrArg f.val h.2)
  simp_rw [he]
  exact (KPGlobalResidualConstruction.NativeComplexHCOperators.hasDerivAt_flow
    KPCplxPrincipalSeriesCharts.positiveParameter _ f.val _).const_mul _

theorem rawStageValue_basis_hasDerivAt
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (b : Fin 6)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) (g : Raw R.A) :
    HasDerivAt (fun t : ℝ => rawStageValue R.A P C s
      (g * localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b t)) x)
      (rawStageValue R.A P C s g (stageLieSlot R P C s w hw b x)) 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    let i : s.val := ⟨Sum.inl w, hw⟩
    let y : ∀ j : s.val, Fiber R.A P C j.val := fun j => localValue R.A P C j.val (g j.val) (x j)
    let L : PiTensorProduct ℂ (fun j : s.val => Fiber R.A P C j.val) →ₗ[ℂ] ℂ :=
      (rationalEvaluation R.A).comp ((comparison R.A P C).comp
        (RestrictedTensorSimple.stageInclusion (Fiber R.A P C) (reference R.A P C) (bad R.A P C) s))
    let E : ℂ →ₗ[ℂ] ℂ := L.comp ((PiTensorProduct.tprod ℂ).toLinearMap y i)
    have hd := (E.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (localValue_basis_hasDerivAt R P C w b (x i) (g (.inl w)))
    have he (t : ℝ) : rawStageValue R.A P C s
        (g * localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b t))
        (PiTensorProduct.tprod ℂ x) =
        E (localValue R.A P C (.inl w) (g (.inl w) * rawBasisExponential R w b t) (x i)) := by
      change L (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ x)) = _
      rw [PiTensorProduct.map_tprod]
      apply congrArg L
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j = i
      · subst j
        simp [localValueMap, y, i, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
          RestrictedProduct.coe_mulSingle_apply]
      · have hj' : j.val ≠ Sum.inl w := fun h => hj (Subtype.ext h)
        simp [localValueMap, y, Function.update_of_ne hj, localToRestricted, RestrictedProduct.mulSingleMonoidHom,
          RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne hj']
    have hv : rawStageValue R.A P C s g
        (stageLieSlot R P C s w hw b (PiTensorProduct.tprod ℂ x)) =
        E (localValue R.A P C (.inl w) (g (.inl w)) (harmonicPlusDerivative b (x i))) := by
      rw [stageLieSlot, tensorSlot_tprod]
      change L (PiTensorProduct.map _ (PiTensorProduct.tprod ℂ _)) = _
      rw [PiTensorProduct.map_tprod]
      apply congrArg L
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j = i
      · subst j; simp [localValueMap, y, i]
      · change (localValueMap R.A P C j.val (g j.val))
          (Function.update x i (harmonicPlusDerivative b (x i)) j) =
          Function.update y i _ j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
        rfl
    have hd' : HasDerivAt (fun t : ℝ => E (localValue R.A P C (.inl w)
        (g (.inl w) * rawBasisExponential R w b t) (x i)))
        (E (localValue R.A P C (.inl w) (g (.inl w)) (harmonicPlusDerivative b (x i)))) 0 := hd
    simpa only [map_smul, he, hv, Pi.smul_apply, Pi.smul_def] using hd'.const_smul c
  | add x y hx hy =>
    simpa only [map_add, Pi.add_apply, Pi.add_def] using hx.add hy

theorem stageLieSlot_transition
    (s t : RestrictedTensorSimple.Level (bad R.A P C)) (hst : s ≤ t)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (b : Fin 6)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
      (bad R.A P C) s t hst (stageLieSlot R P C s w hw b x) =
    stageLieSlot R P C t w (hst hw) b
      (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C)
        (bad R.A P C) s t hst x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [map_smul]
    congr 1
    rw [stageLieSlot, tensorSlot_tprod, RestrictedTensorSimple.transition,
      RestrictedTensorSimple.insert_pure, RestrictedTensorSimple.insert_pure,
      stageLieSlot, tensorSlot_tprod]
    congr 1
    funext j
    by_cases hj : j.val = Sum.inl w
    · have he : j = (⟨Sum.inl w, hst hw⟩ : t.val) := Subtype.ext hj
      subst j
      simp only [Function.update_self, dite_eq_left hw]
    · have hji : j ≠ (⟨Sum.inl w, hst hw⟩ : t.val) := fun h => hj (congrArg Subtype.val h)
      rw [Function.update_of_ne hji]
      split_ifs with hs
      · rw [Function.update_of_ne (show (⟨j.val, hs⟩ : s.val) ≠ ⟨Sum.inl w, hw⟩ from
          fun h => hj (congrArg Subtype.val h))]
      · rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem rawCoreInsertion_stage_basis_hasDerivAt
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) (b : Fin 6)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) (g : Raw R.A) :
    HasDerivAt (fun τ : ℝ => rawCoreInsertion R.A P C
      (RestrictedTensorSimple.stageInclusion _ _ _ s x)
      (g * localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b τ)))
      (rawCoreInsertion R.A P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s (stageLieSlot R P C s w hw b x)) g) 0 := by
  obtain ⟨u, hu⟩ := exists_reference_stage R.A P C g
  let t : RestrictedTensorSimple.Level (bad R.A P C) :=
    ⟨s.val ∪ u.val, s.property.trans Finset.subset_union_left⟩
  have hst : s ≤ t := Finset.subset_union_left
  have ht : ∀ v, v ∉ t.val → localValue R.A P C v (g v) (plusReference R.A P C v) = reference R.A P C v :=
    fun v hv => hu v (fun h => hv (Finset.mem_union_right _ h))
  have hcurve (τ : ℝ) : ∀ v, v ∉ t.val → localValue R.A P C v
      ((g * localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b τ)) v)
      (plusReference R.A P C v) = reference R.A P C v := by
    intro v hv
    have hvw : v ≠ Sum.inl w := fun h => hv (h ▸ hst hw)
    change localValue R.A P C v (g v *
      localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b τ) v)
      (plusReference R.A P C v) = _
    rw [show localToRestricted F ζ hζ (.inl w) (rawBasisExponential R w b τ) v = 1 from
      RestrictedProduct.mulSingle_eq_of_ne _ _ hvw, mul_one]
    exact ht v hv
  have hi (y : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s y =
      RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) t
        (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst y) :=
    Module.DirectLimit.of_f.symm
  simp_rw [hi, rawCoreInsertion_stage R.A P C t _ _ (hcurve _),
    rawCoreInsertion_stage R.A P C t _ g ht, stageLieSlot_transition R P C s t hst w hw b]
  exact rawStageValue_basis_hasDerivAt R P C t w (hst hw) b _ g

theorem quotientCoreEvaluator_stage_actualRight
    (s : RestrictedTensorSimple.Level (bad R.A P C))
    (i : Fin (KPContActualSphericalRightFieldIdentification.groupDimension F))
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    KPContActualSphericalRightFieldIdentification.actualRight F ζ hζ i
      (quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s x)) =
    quotientCoreEvaluator R.A P C (RestrictedTensorSimple.stageInclusion _ _ _ s
      (stageLieSlot R P C s (actualLieIndexEquiv (F := F) i).1
        (s.property (by
          simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
        (actualLieIndexEquiv (F := F) i).2 x)) := by
  funext g
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      unfold KPContActualSphericalRightFieldIdentification.actualRight
      simp_rw [rawBasisExponential_actual_path R i]
      have he (τ : ℝ) :
          scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
            scalarQuotient F ζ hζ (localInjection F ζ hζ
              (.inl (actualLieIndexEquiv (F := F) i).1)
              (rawBasisExponential R (actualLieIndexEquiv (F := F) i).1
                (actualLieIndexEquiv (F := F) i).2 τ)) =
          scalarQuotient F ζ hζ (amalgamation F ζ hζ
            (g * localToRestricted F ζ hζ (.inl (actualLieIndexEquiv (F := F) i).1)
              (rawBasisExponential R (actualLieIndexEquiv (F := F) i).1
                (actualLieIndexEquiv (F := F) i).2 τ))) := by
        change _ * scalarQuotient F ζ hζ (amalgamation F ζ hζ _) = _
        rw [map_mul, map_mul]
      have hefun : (fun τ : ℝ => quotientCoreEvaluator R.A P C
          (RestrictedTensorSimple.stageInclusion _ _ _ s x)
          (scalarQuotient F ζ hζ (amalgamation F ζ hζ g) *
            scalarQuotient F ζ hζ (localInjection F ζ hζ
              (.inl (actualLieIndexEquiv (F := F) i).1)
              (rawBasisExponential R (actualLieIndexEquiv (F := F) i).1
                (actualLieIndexEquiv (F := F) i).2 τ)))) =
          (fun τ : ℝ => rawCoreInsertion R.A P C
            (RestrictedTensorSimple.stageInclusion _ _ _ s x)
            (g * localToRestricted F ζ hζ (.inl (actualLieIndexEquiv (F := F) i).1)
              (rawBasisExponential R (actualLieIndexEquiv (F := F) i).1
                (actualLieIndexEquiv (F := F) i).2 τ))) := by
        funext τ
        rw [he τ]
        rfl
      have hd := (rawCoreInsertion_stage_basis_hasDerivAt R P C s
        (actualLieIndexEquiv (F := F) i).1
        (s.property (by simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad]))
        (actualLieIndexEquiv (F := F) i).2 x g).deriv
      exact (congrArg (fun f : ℝ → ℂ => deriv f 0) hefun).trans hd

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
