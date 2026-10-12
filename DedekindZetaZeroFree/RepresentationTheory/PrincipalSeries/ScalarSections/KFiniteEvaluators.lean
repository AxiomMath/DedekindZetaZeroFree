module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.TensorMaximalCompactActions

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField IsDedekindDomain KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

def stageScalarInsertion (s : RestrictedTensorSimple.Level (bad R.A P C)) :
    RestrictedTensorSimple.Stage (Plus R.A P C) s.val →ₗ[ℂ]
      KPLiteralRaw.Functions F R.A.zeta12 R.A.primitive_zeta12 :=
  (quotientCoreEvaluator R.A P C).comp
    (RestrictedTensorSimple.stageInclusion (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s)

theorem stageScalarInsertion_maxAction (s : RestrictedTensorSimple.Level (bad R.A P C))
    (k : ThetaExpansion.fullProductCompactPreimage R)
    (hfix : ∀ v, v ∉ s.val →
      localMaxAction R P C v ⟨k.val v, k.property v⟩ (plusReference R.A P C v) =
        plusReference R.A P C v)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 k.val))
      (stageScalarInsertion R P C s x) =
    stageScalarInsertion R P C s
      (stageMaxAction R P C s (fun j => ⟨k.val j.val, k.property j.val⟩) x) := by
  funext g
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      change quotientCoreValue R.A P C
        (RestrictedTensorSimple.stageInclusion _ _ _ s x)
        (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g) *
        KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 k.val)) = _
      rw [← map_mul, ← map_mul]
      exact (rawCoreInsertion_maxAction R P C s k g hfix x).symm

theorem reference_fixed_outside (s : RestrictedTensorSimple.Level (bad R.A P C))
    (hgood : ∀ q : KPFinitePlace F, Sum.inr q ∉ s.val → ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (k : ThetaExpansion.fullProductCompactPreimage R) :
    ∀ v, v ∉ s.val →
      localMaxAction R P C v ⟨k.val v, k.property v⟩ (plusReference R.A P C v) =
        plusReference R.A P C v := by
  intro v hv
  have hb : v ∉ bad R.A P C := fun h => hv (s.property h)
  cases v with
  | inl w => simp [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad] at hb
  | inr q =>
    apply finiteMax_reference R P C q
    · simpa [bad, KPGlobalResidualConstruction.ScalarAbsorption.fullBad] using hb
    · exact hgood q hv

theorem stageScalarInsertion_kFinite (s : RestrictedTensorSimple.Level (bad R.A P C))
    (hgood : ∀ q : KPFinitePlace F, Sum.inr q ∉ s.val → ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (x : RestrictedTensorSimple.Stage (Plus R.A P C) s.val) :
    KPLiteralRaw.KFinite F R.A.zeta12 R.A.primitive_zeta12 (ThetaExpansion.fullProductCompact R)
      (stageScalarInsertion R P C s x) := by
  obtain ⟨U, hU, hx, hstable⟩ := stageMax_finite_subspace R P C s x
  let : Module.Finite ℂ U := hU
  let inc := (stageScalarInsertion R P C s).comp U.subtype
  refine ⟨inc.range, inferInstance, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
  intro k y hy
  obtain ⟨z, rfl⟩ := hy
  obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.mp k.property
  let ak : ThetaExpansion.fullProductCompactPreimage R := ⟨a, ha⟩
  let ks (j : s.val) : ThetaExpansion.iwasawaCompactFactor R j.val := ⟨ak.val j.val, ak.property j.val⟩
  refine ⟨⟨stageMaxAction R P C s ks z.val, hstable ks z.val z.property⟩, ?_⟩
  change stageScalarInsertion R P C s (stageMaxAction R P C s ks z.val) =
    KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 k.val
      (stageScalarInsertion R P C s z.val)
  rw [← hak]
  exact (stageScalarInsertion_maxAction R P C s ak (reference_fixed_outside R P C s hgood ak) z.val).symm

theorem quotientCoreEvaluator_kFinite
    (x : RestrictedTensorSimple.Core (Plus R.A P C) (plusReference R.A P C) (bad R.A P C)) :
    KPLiteralRaw.KFinite F R.A.zeta12 R.A.primitive_zeta12 (ThetaExpansion.fullProductCompact R)
      (quotientCoreEvaluator R.A P C x) := by
  let : Nonempty (RestrictedTensorSimple.Level (bad R.A P C)) := ⟨⟨bad R.A P C, le_rfl⟩⟩
  induction x using Module.DirectLimit.induction_on with
  | ih s x =>
    let E : Finset (KPHilbert.Place F) := (KPAdelicCoverRestrictedProduct.bad_finite F).toFinset.image Sum.inr
    let t : RestrictedTensorSimple.Level (bad R.A P C) :=
      ⟨s.val ∪ E, s.property.trans Finset.subset_union_left⟩
    have hst : s ≤ t := Finset.subset_union_left
    have hgood : ∀ q : KPFinitePlace F, Sum.inr q ∉ t.val → ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro q hq hb
      exact hq (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨q, (Set.Finite.mem_toFinset _).mpr hb, rfl⟩))
    change KPLiteralRaw.KFinite _ _ _ _ (stageScalarInsertion R P C s x)
    have he : stageScalarInsertion R P C s x = stageScalarInsertion R P C t
        (RestrictedTensorSimple.transition (Plus R.A P C) (plusReference R.A P C) (bad R.A P C) s t hst x) :=
      congrArg (quotientCoreEvaluator R.A P C) Module.DirectLimit.of_f.symm
    rw [he]
    exact stageScalarInsertion_kFinite R P C t hgood _

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
