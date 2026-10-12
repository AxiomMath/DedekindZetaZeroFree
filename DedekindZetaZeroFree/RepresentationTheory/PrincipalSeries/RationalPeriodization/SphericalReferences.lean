module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RationalPeriodization.FiberComparison
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalGoodSphericalImage
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem value_one_fixed (q : KPFinitePlace F)
    (f : plusLocal R (imageData R N P C) (Sum.inr q))
    (hf : f ∈ fixedSubmodule (IPlus (C.canonical q).borel (C.polarization q))
      (C.canonical q).iwasawa.compact.toOpenSubgroup) :
    f.val 1 ∈ fixedSubmodule (tau (C.polarization q))
      (compactTorus (C.canonical q).borel (C.canonical q).iwasawa) := by
  intro j
  have hj : ((C.canonical q).borel.torus j.val :
      KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := j.property
  have hfix := congrArg (fun u : plusLocal R (imageData R N P C) (Sum.inr q) => u.val 1)
    (hf ⟨(C.canonical q).borel.torus j.val, hj⟩)
  have hcov := f.property.1 ((C.canonical q).borel.torus j.val) 1
  have hs : inducingScalar (C.canonical q).borel 0 ((C.canonical q).borel.torus j.val) = 1 := by
    simp [inducingScalar, deltaHalf, normPower, (C.canonical q).iwasawa.intersection_norm _ hj]
  change f.val (1 * (C.canonical q).borel.torus j.val) = f.val 1 at hfix
  rw [mul_one] at hcov
  rw [one_mul] at hfix
  change f.val ((C.canonical q).borel.torus j.val) =
    inducingScalar (C.canonical q).borel 0 ((C.canonical q).borel.torus j.val) •
      tau (C.polarization q) ((C.canonical q).borel.retract
        ((C.canonical q).borel.torus j.val)) (f.val 1) at hcov
  rw [hs, one_smul, (C.canonical q).borel.retract_torus] at hcov
  exact hcov.symm.trans hfix

theorem normalized_section (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    ∃ f : plusLocal R (imageData R N P C) (Sum.inr q),
      f ∈ fixedSubmodule (IPlus (C.canonical q).borel (C.polarization q))
        (C.canonical q).iwasawa.compact.toOpenSubgroup ∧
      f.val 1 = localReference F R.A.zeta12 R.A.primitive_zeta12 P C q := by
  obtain ⟨f, hf, _⟩ := normalized_plus_spherical_vector (C.canonical q).borel
    (C.polarization q) (C.canonical q).iwasawa (C.unramified q hq)
  exact ⟨f, hf.1,
    (referenceGoodSpherical F R.A.zeta12 R.A.primitive_zeta12 P C q hq).2.2
      (f.val 1) (value_one_fixed R N P C q f hf.1) hf.2⟩

def plusReference : ∀ p, plusLocal R (imageData R N P C) p
  | Sum.inl _ => ⟨KPCplxPrincipalSeriesCharts.sphericalSection
      KPCplxPrincipalSeriesCharts.positiveParameter, by
      apply le_iSup (KPCplxIntertwinerEigenvalues.harmonicKType
        KPCplxPrincipalSeriesCharts.positiveParameter) 0
      rw [KPCplxIntertwinerEigenvalues.harmonicKType_zero_eq_span]
      exact Submodule.subset_span (Set.mem_singleton _)⟩
  | Sum.inr q => if hq : q ∉ C.exceptional then (normalized_section R N P C q hq).choose else 0

theorem finite_not_bad (q : KPFinitePlace F) (hq : Sum.inr q ∉ bad R P C) :
    q ∉ C.exceptional := by
  intro h
  exact hq (PrincipalOfKP.ResidueCoreBridge.CanonicalBinding.finite_mem_badSet
    F R.A.zeta12 R.A.primitive_zeta12 P C q h)

theorem plusReference_one (q : KPFinitePlace F) (hq : Sum.inr q ∉ bad R P C) :
    (plusReference R N P C (Sum.inr q)).val 1 = reference R P C (Sum.inr q) := by
  rw [plusReference, dif_pos (finite_not_bad R P C q hq)]
  exact (normalized_section R N P C q (finite_not_bad R P C q hq)).choose_spec.2

def tame (q : KPFinitePlace F) (hq : Sum.inr q ∉ bad R P C) :
    ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3 :=
  (C.actual_compact q (finite_not_bad R P C q hq)).choose

theorem plusReference_spherical (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (k : KPTameCompact.K0 F q) :
    IPlus (imageData R N P C q).inducing.borel (imageData R N P C q).inducing.polarization
      (KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12 R.A.primitive_zeta12
        q (tame R P C q hq) k) (plusReference R N P C (Sum.inr q)) =
      plusReference R N P C (Sum.inr q) := by
  have hc := (C.actual_compact q (finite_not_bad R P C q hq)).choose_spec
  have hk : KPLocalExceptionalConstruction.actualGoodCompactSplit F R.A.zeta12
      R.A.primitive_zeta12 q (tame R P C q hq) k ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup :
      Subgroup (KPLocalExceptionalConstruction.ActualCover F R.A.zeta12 R.A.primitive_zeta12 q))
    rw [hc]
    exact MonoidHom.mem_range.mpr ⟨k, rfl⟩
  rw [plusReference, dif_pos (finite_not_bad R P C q hq)]
  exact (normalized_section R N P C q (finite_not_bad R P C q hq)).choose_spec.1 ⟨_, hk⟩

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
