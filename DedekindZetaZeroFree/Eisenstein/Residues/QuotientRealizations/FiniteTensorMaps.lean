module

public import DedekindZetaZeroFree.Eisenstein.Residues.QuotientRealizations.RestrictedTensorDescent
public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource

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

theorem dictionary_of_source_stages
    (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (e : ∀ p, plusLocal R M p) (bad : Finset (KPHilbert.Place F))
    (hbad : ∀ p, p ∈ bad ↔ (∃ w : InfinitePlace F, p = Sum.inl w) ∨
      (∃ q : KPFinitePlace F, p = Sum.inr q ∧ q ∈ R.A.Sf))
    (slot : R.A.Sf)
    (L : ∀ s : RestrictedTensorSimple.Level bad,
      RestrictedTensorSimple.Stage (plusLocal R M) s.val →ₗ[ℂ] Functions R)
    (hL : ∀ s t (hst : s ≤ t) x,
      L t (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x) = L s x)
    (hlocal : ∀ (s : RestrictedTensorSimple.Level bad)
      (x : ∀ p : s.val, plusLocal R M p) (p : s.val),
      sourceQuotient R M p (x p) = 0 → L s (PiTensorProduct.tprod ℂ x) = 0)
    (a : R.A.UnitQuotient → ∀ p : bad, plusLocal R M p)
    (ha : ∀ v, L ⟨bad, le_rfl⟩ (PiTensorProduct.tprod ℂ (a v)) =
      D.realization.theta v) :
    ∃ B : Dictionary R N, B.toPeriodSource = D ∧
      B.coreMap (B.selected B.probe) ≠ 0 := by
  obtain ⟨b, hb, _⟩ := sourceCore_descent R M e bad L hL hlocal
  let references := fun p => sourceQuotient R M p (e p)
  let s : RestrictedTensorSimple.Level bad := ⟨bad, le_rfl⟩
  let selected := fun v => RestrictedTensorSimple.stageInclusion (actualLocal R M)
    references bad s (sourceStageQuotient R M bad (PiTensorProduct.tprod ℂ (a v)))
  have hs (v) : b (selected v) = D.realization.theta v :=
    (hb s (PiTensorProduct.tprod ℂ (a v))).trans (ha v)
  let B : Dictionary R N := {
    toPeriodSource := D
    finiteData := M
    references := references
    bad := bad
    bad_exact := hbad
    scalarSlot := slot
    coreMap := b
    selected := selected
    selected_eq := hs
    selected_frozen_stage := by
      intro v
      refine ⟨s, fun p => sourceQuotient R M p (a v p), rfl, ?_⟩
      simp only [selected, sourceStageQuotient, PiTensorProduct.map_tprod]
      rfl }
  exact ⟨B, rfl, B.image_ne⟩

theorem dictionary_of_realized_source_stages
    (D : PeriodSource R N) (M : ∀ q, LocalImageData R q)
    (e : ∀ p, plusLocal R M p) (bad : Finset (KPHilbert.Place F))
    (hbad : ∀ p, p ∈ bad ↔ (∃ w : InfinitePlace F, p = Sum.inl w) ∨
      (∃ q : KPFinitePlace F, p = Sum.inr q ∧ q ∈ R.A.Sf))
    (slot : R.A.Sf)
    (A : ∀ s : RestrictedTensorSimple.Level bad,
      RestrictedTensorSimple.Stage (plusLocal R M) s.val →ₗ[ℂ]
        SharedSource.flatScalarStage D.sources)
    (hA : ∀ s t (hst : s ≤ t) x,
      A t (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x) = A s x)
    (hlocal : ∀ (s : RestrictedTensorSimple.Level bad)
      (x : ∀ p : s.val, plusLocal R M p) (p : s.val),
      sourceQuotient R M p (x p) = 0 →
        (SharedSource.realizedSourceResidue D.realization (A s (PiTensorProduct.tprod ℂ x))).val = 0)
    (a : R.A.UnitQuotient → ∀ p : bad, plusLocal R M p)
    (ha : ∀ v, A ⟨bad, le_rfl⟩ (PiTensorProduct.tprod ℂ (a v)) =
      ⟨(D.sources.flat v).val 0, Submodule.subset_span ⟨v, rfl⟩⟩) :
    ∃ B : Dictionary R N, B.toPeriodSource = D ∧
      B.coreMap (B.selected B.probe) ≠ 0 := by
  let L := fun s => (FourierContinuation.translateSpan D.realization).subtype.comp
    ((SharedSource.realizedSourceResidue D.realization).comp (A s))
  refine dictionary_of_source_stages D M e bad hbad slot L ?_ hlocal a ?_
  · intro s t hst x
    change (SharedSource.realizedSourceResidue D.realization
      (A t (RestrictedTensorSimple.transition (plusLocal R M) e bad s t hst x))).val = _
    rw [hA]
    rfl
  · intro v
    change (SharedSource.realizedSourceResidue D.realization
      (A ⟨bad, le_rfl⟩ (PiTensorProduct.tprod ℂ (a v)))).val = _
    rw [ha]
    exact SharedSource.realizedSourceResidue_companion D.realization v

end DedekindZetaZeroFree.FourierContinuation.DetectedDictionary

end
