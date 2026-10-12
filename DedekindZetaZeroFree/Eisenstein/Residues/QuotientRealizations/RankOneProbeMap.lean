module

public import DedekindZetaZeroFree.Eisenstein.Residues.QuotientRealizations.FiniteTensorMaps
public import DedekindZetaZeroFree.Theta.Periods.RepeatedProbeFamily
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Quotients.ReferenceCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.DetectedDictionary
open MomentSources TensorActionSource NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def probeSourceStage (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (bad : Finset (KPHilbert.Place F)) (s : RestrictedTensorSimple.Level bad) :
    RestrictedTensorSimple.Stage (plusLocal R M) s.val →ₗ[ℂ]
      SharedSource.flatScalarStage (repeatedProbe D).sources :=
  (FourierContinuation.stageFunctional (plusLocal R M) (sourceReferenceForm R M) s.val).smulRight
    ⟨(D.sources.flat D.probe).val 0, Submodule.subset_span ⟨D.probe, rfl⟩⟩

theorem probeSourceStage_insertion (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (bad : Finset (KPHilbert.Place F))
    (s t : RestrictedTensorSimple.Level bad) (hst : s ≤ t) (x) :
    probeSourceStage D M bad t
        (RestrictedTensorSimple.transition (plusLocal R M) (referenceSource R M) bad s t hst x) =
      probeSourceStage D M bad s x := by
  have h := LinearMap.congr_fun (FourierContinuation.stageFunctional_insert (plusLocal R M)
    (referenceSource R M) bad (sourceReferenceForm R M)
    (fun p _ => sourceReferenceForm_reference R M p) s t hst) x
  simp only [probeSourceStage, LinearMap.smulRight_apply]
  exact congrArg (fun c : ℂ => c •
    (⟨(D.sources.flat D.probe).val 0, Submodule.subset_span ⟨D.probe, rfl⟩⟩ :
      SharedSource.flatScalarStage (repeatedProbe D).sources)) h

theorem probeSourceStage_kernel (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (bad : Finset (KPHilbert.Place F)) (s : RestrictedTensorSimple.Level bad)
    (x : ∀ p : s.val, plusLocal R M p) (p : s.val)
    (hp : sourceQuotient R M p (x p) = 0) :
    probeSourceStage D M bad s (PiTensorProduct.tprod ℂ x) = 0 := by
  have hz : sourceReferenceForm R M p (x p) = 0 := sourceReferenceForm_kernel R M p _ hp
  simp only [probeSourceStage, LinearMap.smulRight_apply, FourierContinuation.stageFunctional_pure]
  have hprod : (∏ j : s.val, sourceReferenceForm R M j (x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ p) hz
  rw [hprod, zero_smul]

theorem probeSourceStage_reference (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (bad : Finset (KPHilbert.Place F)) (v : R.A.UnitQuotient) :
    probeSourceStage D M bad ⟨bad, le_rfl⟩
      (PiTensorProduct.tprod ℂ (fun p : bad => referenceSource R M p)) =
        (⟨((repeatedProbe D).sources.flat v).val 0,
          Submodule.subset_span ⟨v, rfl⟩⟩ : SharedSource.flatScalarStage (repeatedProbe D).sources) := by
  simp only [probeSourceStage, LinearMap.smulRight_apply, FourierContinuation.stageFunctional_pure,
    sourceReferenceForm_reference, Finset.prod_const_one, one_smul]
  rfl

theorem dictionary_for_named_probe (D : PeriodSource R N) :
    ∃ B : Dictionary R N, B.toPeriodSource = repeatedProbe D ∧
      B.coreMap (B.selected B.probe) ≠ 0 := by
  let M := TensorSeedSource.localData R
  let bad := TensorSeedSource.bad R
  exact dictionary_of_realized_source_stages
    (repeatedProbe D) M (referenceSource R M) bad (TensorSeedSource.bad_exact R)
    (TensorSeedSource.scalarSlot R) (probeSourceStage D M bad)
    (probeSourceStage_insertion D M bad)
    (by
      intro s x p hp
      rw [probeSourceStage_kernel D M bad s x p hp, map_zero]
      rfl)
    (fun _ p => referenceSource R M p)
    (probeSourceStage_reference D M bad)

theorem detected_dictionary_exists (prior : Nonempty (PeriodSource R N)) :
    ∃ B : Dictionary R N, B.coreMap (B.selected B.probe) ≠ 0 := by
  obtain ⟨D⟩ := prior
  obtain ⟨B, _, hB⟩ := dictionary_for_named_probe D
  exact ⟨B, hB⟩

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end
