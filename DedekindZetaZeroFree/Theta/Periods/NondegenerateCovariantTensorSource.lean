module

public import DedekindZetaZeroFree.Eisenstein.Residues.FourierPeriodExtraction
public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.Eisenstein.Residues.RealizationAndPeriods

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct Topology
open NumberField Filter MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.NonDegenerate
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

structure PeriodSource extends JointRealizedFlatSources R N where
  probe : R.A.UnitQuotient
  coefficient : ℂ
  coefficient_ne : coefficient ≠ 0
  period_limit : Tendsto (fun z : ℂ => z * fourier R sources.dq
    (realization.E probe z) 1) (nhdsWithin 0 {0}ᶜ) (nhds coefficient)

namespace PeriodSource
variable {R N}

theorem period_eq (D : PeriodSource R N) :
    fourier R D.sources.dq (D.realization.theta D.probe) 1 = D.coefficient := by
  exact tendsto_nhds_unique (fourier_residue_tendsto D.realization D.probe 1) D.period_limit

theorem detected (D : PeriodSource R N) :
    fourier R D.sources.dq (D.realization.theta D.probe) 1 ≠ 0 := by
  rw [D.period_eq]
  exact D.coefficient_ne

theorem residue_ne (D : PeriodSource R N) : D.realization.theta D.probe ≠ 0 := by
  intro hz
  apply D.detected
  simp [hz, MomentSources.fourier]

theorem flat_ne (D : PeriodSource R N) : (D.sources.flat D.probe).val 0 ≠ 0 := by
  intro hz
  have hx : (⟨(D.sources.flat D.probe).val 0,
      Submodule.subset_span ⟨D.probe, rfl⟩⟩ : SharedSource.flatScalarStage D.sources) = 0 :=
    Subtype.ext hz
  have h := SharedSource.realizedSourceResidue_companion D.realization D.probe
  rw [hx, map_zero] at h
  exact D.residue_ne h.symm

theorem integrable (D : PeriodSource R N) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => D.realization.theta D.probe
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ)) D.sources.dq :=
  theta_period_integrable D.realization D.probe g
end PeriodSource

structure Dictionary extends PeriodSource R N where
  finiteData : ∀ q, LocalImageData R q
  references : ∀ p, actualLocal R finiteData p
  bad : Finset (KPHilbert.Place F)
  bad_exact : ∀ p, p ∈ bad ↔ (∃ w : InfinitePlace F, p = Sum.inl w) ∨
    (∃ q : KPFinitePlace F, p = Sum.inr q ∧ q ∈ R.A.Sf)
  scalarSlot : R.A.Sf
  coreMap : RestrictedTensorSimple.Core (actualLocal R finiteData) references bad →ₗ[ℂ] Functions R
  selected : R.A.UnitQuotient → RestrictedTensorSimple.Core (actualLocal R finiteData) references bad
  selected_eq : ∀ v, coreMap (selected v) = realization.theta v
  selected_frozen_stage : ∀ v, ∃ (s : RestrictedTensorSimple.Level bad)
    (x : ∀ p : s.val, actualLocal R finiteData p), s.val = bad ∧
      selected v = RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x)

namespace Dictionary
variable {R N}
theorem image_ne (D : Dictionary R N) : D.coreMap (D.selected D.probe) ≠ 0 := by
  rw [D.selected_eq]
  exact D.toPeriodSource.residue_ne

theorem selected_ne (D : Dictionary R N) : D.selected D.probe ≠ 0 := by
  intro hz
  exact D.image_ne (by rw [hz, map_zero])

theorem core_not_subsingleton (D : Dictionary R N) :
    ¬ Subsingleton (RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad) := by
  intro h
  exact D.selected_ne (@Subsingleton.elim _ h _ _)

theorem reference_ne_zero (D : Dictionary R N) (p : KPHilbert.Place F)
    (hp : p ∉ D.bad) : D.references p ≠ 0 := by
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage D.probe
  have hps : p ∉ s.val := by rwa [hs]
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert p s.val, s.property.trans (Finset.subset_insert _ _)⟩
  let y : ∀ j : t.val, actualLocal R D.finiteData j :=
    fun j => if h : j.val ∈ s.val then x ⟨j.val, h⟩ else D.references j
  have htrans : RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (PiTensorProduct.tprod ℂ y) = D.selected D.probe := by
    rw [hx, ← RestrictedTensorSimple.insert_pure (actualLocal R D.finiteData)
      D.references s.val t.val (Finset.subset_insert p s.val) x]
    exact Module.DirectLimit.of_f
  intro hz
  have hy : y ⟨p, Finset.mem_insert_self _ _⟩ = 0 := by simp [y, hps, hz]
  have hzero : PiTensorProduct.tprod ℂ y = 0 :=
    (PiTensorProduct.tprod ℂ).map_coord_zero ⟨p, Finset.mem_insert_self _ _⟩ hy
  exact D.selected_ne (by rw [← htrans, hzero, map_zero])

theorem initial_pure_nonzero (D : Dictionary R N) :
    ∃ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ p : s.val, actualLocal R D.finiteData p),
      s.val = D.bad ∧
      D.selected D.probe = RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ x) ∧
      PiTensorProduct.tprod ℂ x ≠ 0 ∧ ∀ p, x p ≠ 0 := by
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage D.probe
  have hn : PiTensorProduct.tprod ℂ x ≠ 0 := by
    intro hz
    exact D.selected_ne (by rw [hx, hz, map_zero])
  refine ⟨s, x, hs, hx, hn, ?_⟩
  intro p hp
  exact hn ((PiTensorProduct.tprod ℂ).map_coord_zero p hp)
end Dictionary

structure Faithful extends Dictionary R N where
  core_injective : Function.Injective coreMap
  regular : ∀ x, coreMap x ∈ regularResidualFunctions R

structure Generated extends Faithful R N where
  generated : ∀ x, coreMap x ∈ hcHeckeSpan realization

namespace Generated
variable {R N}
def tensorHC (D : Generated R N) : TensorHC R N where
  toJointRealizedFlatSources := D.toJointRealizedFlatSources
  finiteData := D.finiteData
  references := D.references
  bad := D.bad
  bad_exact := D.bad_exact
  scalarSlot := D.scalarSlot
  coreMap := D.coreMap
  selected := D.selected
  selected_eq := D.selected_eq
  selected_frozen_stage := D.selected_frozen_stage
  core_injective := D.core_injective
  regular := D.regular
  generated := D.generated

theorem same_residue (D : Generated R N) (x) :
    D.coreMap x ∈ sameResidueModule D.realization :=
  ⟨D.generated x, D.regular x⟩

theorem integrable (D : Generated R N) (x) (g : Group R) :
    Integrable (fun q : KPAdditiveQuotient F => D.coreMap x
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out q) * g) * star (adelicTraceQuotientCharacter F q : ℂ)) D.sources.dq :=
  sameResidue_period_integrable D.realization (D.same_residue x) g
end Generated

structure FiniteCovariant extends Generated R N where
  finite_intertwining : ∀ q (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (s : RestrictedTensorSimple.Level bad) (hq : Sum.inr q ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q (finiteData q).inducing (finiteData q).inducing.polarization
          (finiteData q).haar (finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a))

structure ComplexCovariant extends FiniteCovariant R N where
  complex_intertwining : ∀ (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (s : RestrictedTensorSimple.Level bad) (hw : Sum.inl w ∈ s.val)
    (x : ∀ p : s.val, actualLocal R finiteData p) g,
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inl w, hw⟩
        (KPGlobalResidualConstruction.complexCoreSU2Action k (x ⟨Sum.inl w, hw⟩))))) g =
    coreMap (RestrictedTensorSimple.stageInclusion _ references bad s (PiTensorProduct.tprod ℂ x))
      (g * KPGlobalResidualConstruction.complexCompactLift F R.A.zeta12 R.A.primitive_zeta12 w k)

def ComplexCovariant.tensorDetected (D : ComplexCovariant R N) : TensorDetected R N where
  toTensorHC := D.toGenerated.tensorHC
  finite_intertwining := D.finite_intertwining
  complex_intertwining := D.complex_intertwining
  detected := ⟨D.probe, D.toPeriodSource.detected⟩

end DedekindZetaZeroFree.FourierContinuation.NonDegenerate

end
