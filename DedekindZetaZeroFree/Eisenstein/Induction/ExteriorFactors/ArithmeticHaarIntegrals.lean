module

public import DedekindZetaZeroFree.Theta.Profiles.SphericalChamberReduction
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.ParameterEvaluation
public import DedekindZetaZeroFree.Metaplectic.Kubota.ArithmeticCompactGenerators
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Iwasawa.NegativeShellCoordinates
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.TameCubicShells

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources KPGlobalTorusFiniteStages KPLocalPrincipalSeries KPLocalExceptionalConstruction
open KPLocalStoneVonNeumann KPRankOneShellContinuation KPRankOneShellRepair
open KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue
open KPLocalTameIntertwiningBlock KPRankOneTameSphericalFactor
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem good_compact_le_full (q : KPFinitePlace F) (hq : q ∉ C.exceptional) :
    ((C.canonical q).iwasawa.compact.toOpenSubgroup :
      Subgroup (ActualCover F R.A.zeta12 R.A.primitive_zeta12 q)) ≤
        (fullCompact R P C q).compact.toOpenSubgroup := by
  obtain ⟨ht, hc⟩ := C.actual_compact q hq
  rw [hc, fullCompact_eq R P C q]
  rintro g ⟨k, rfl⟩
  change KPPGLLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (.inr q) _ ∈
    KPRankOneCartanGeometry.K0 F q
  rw [actualGoodCompactSplit, MonoidHom.comp_apply,
    KPPGLLocalCover.projection_coverQuotient, KPGoodCompactSplitting.projection_kStar]
  exact ⟨k, rfl⟩

theorem good_forwardAbs_eq (q : KPFinitePlace F) (hq : q ∉ C.exceptional)
    (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (fullCompact R P C q) g =
    LocalCompactChange.forwardAbs F R.A.zeta12 R.A.primitive_zeta12 q
      (C.canonical q) (C.canonical q).iwasawa g := by
  let k := (C.canonical q).iwasawa.compactPart g
  let k' : (fullCompact R P C q).compact.toOpenSubgroup :=
    ⟨k.val, good_compact_le_full R P C q hq k.property⟩
  have h := LocalCompactChange.forwardAbs_factorization F R.A.zeta12
    R.A.primitive_zeta12 q (C.canonical q) (fullCompact R P C q)
    ((C.canonical q).iwasawa.borelPart g) k'
  rw [← (C.canonical q).iwasawa.decomposition g] at h
  exact h

def exteriorProfile (q : KPFinitePlace F) :
    compactPicture (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus :=
  (compactTrivialization (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus 0).symm (plusReference R N P C (.inr q))

theorem exteriorProfile_spherical (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) :
    IsSphericalVector (LocalField F q) (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus (exteriorProfile R N P C q) := by
  apply (is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mpr
  refine ⟨?_, ?_⟩
  · apply (compact_level_identification (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus (C.canonical q).iwasawa.compact le_rfl 0 _).mpr
    rw [exteriorProfile, LinearEquiv.apply_symm_apply,
      plusReference, dif_pos (finite_not_bad R P C q hq)]
    exact (normalized_section R N P C q (finite_not_bad R P C q hq)).choose_spec.1
  · change ((plusReference R N P C (.inr q)).val 1).val 1 = 1
    rw [plusReference_one R N P C q hq]
    exact (referenceGoodSpherical F R.A.zeta12 R.A.primitive_zeta12 P C q
      (finite_not_bad R P C q hq)).2.1

theorem exterior_parameter_input (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (z : ℂ)
    (g : ActualCover F R.A.zeta12 R.A.primitive_zeta12 q) :
    (finiteParameterInput R N P C q (fullCompact R P C q) z
      (plusReference R N P C (.inr q))).val g =
    (compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus z (exteriorProfile R N P C q)).val g := by
  rw [finiteParameterInput_displacement,
    good_forwardAbs_eq R P C q (finite_not_bad R P C q hq)]
  conv_rhs => rw [FiniteDisplacement.compact_extension_displacement]
  rw [exteriorProfile, LinearEquiv.apply_symm_apply]
  rfl

open _root_.DedekindZetaZeroFree.KPExceptionalRaw renaming root → root
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming minus_fiber_fixed → minus_fiber_fixed
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming compact_extension_value → compact_extension_value

theorem exterior_integer_integral (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (z : ℂ) (hz : convergenceHalfPlane .plus z)
    (t : actualTorus F R.A.zeta12 R.A.primitive_zeta12 q) :
    (∫ x : LocalField F q,
      ((compactTrivialization (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa .plus z (exteriorProfile R N P C q)).val
          ((C.canonical q).borel.liftedW⁻¹ *
            (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t
      ∂integerHaar R N q) =
    forwardFactor (LocalField F q) (integerHaar R N q) z * (reference R P C (.inr q)).val t := by
  have hcq := finite_not_bad R P C q hq
  obtain ⟨ht, hcompact⟩ := C.actual_compact q hcq
  obtain ⟨hw, hn⟩ := kernel_generators_mem_of_actual_compact F R.A.zeta12
    R.A.primitive_zeta12 q (C.canonical q) ht hcompact
  have hcoord := negative_shell_iwasawa_coordinate F R.A.zeta12 R.A.primitive_zeta12
    q (C.canonical q) hw hn
  let φp := exteriorProfile R N P C q
  have hp := exteriorProfile_spherical R N P C q hq
  have hzero := tame_spherical_zero_shells_of_actual_compact F R.A.zeta12
    R.A.primitive_zeta12 q (C.canonical q) (C.polarization q)
    (integerHaar R N q) (integerHaar_integer R N q) ht hcompact φp hp
  obtain ⟨ξ, _, hξ⟩ := root F R.A.zeta12 R.A.primitive_zeta12 q
  have hc := spherical_scalar_of_cubic_shell_integrals F R.A.zeta12 R.A.primitive_zeta12
    q (C.canonical q) (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q) φp hp
    (fun u _ => spherical_integer_ball_integral (LocalField F q)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa
      (integerHaar R N q) φp hp hw hn u)
    (fun u _ n => spherical_shell_integral_deformation (LocalField F q)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa
      (integerHaar R N q) φp hcoord hzero u n)
  have hW := compact_torus_weyl_stable (LocalField F q)
    (C.canonical q).borel (C.canonical q).iwasawa hw
  obtain ⟨φm, hm⟩ := exists_minus_spherical_vector (LocalField F q)
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa (C.unramified q hcq) hW
  have hch := FourierContinuation.CurrentSphericalReduction.actual_spherical_chamber F R.A.zeta12
    R.A.primitive_zeta12 q (C.canonical q) (C.polarization q)
    (integerHaar R N q) (integerHaar_integer R N q) (C.unramified q hcq) hW φp φm hp hm hc
  have hv := hch z hz 1 t
  have hmval : φm.val 1 = reference R P C (.inr q) :=
    (referenceGoodSpherical F R.A.zeta12 R.A.primitive_zeta12 P C q hcq).2.2 _
      (minus_fiber_fixed (LocalField F q) (C.canonical q).borel (C.polarization q)
        (C.canonical q).iwasawa hW φm
        ((is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mp hm).1)
      ((is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mp hm).2
  have he := compact_extension_value (LocalField F q) (C.canonical q).borel
    (C.polarization q) (C.canonical q).iwasawa .minus (-z) φm 1
  simp only [Subgroup.coe_one] at he
  rw [he, hmval] at hv
  exact hv

theorem exterior_arithmetic_integral (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ bad R P C) (z : ℂ) (hz : z ∈ KPContinuation.spectralDomain)
    (t : actualTorus F R.A.zeta12 R.A.primitive_zeta12 q) :
    Integrable (fun x : LocalField F q =>
      ((finiteParameterInput R N P C q (fullCompact R P C q) z
        (plusReference R N P C (.inr q))).val
          ((C.canonical q).borel.liftedW⁻¹ *
            (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t)
      (arithmeticRootMeasure R N (.inr q)) ∧
    (∫ x : LocalField F q,
      ((finiteParameterInput R N P C q (fullCompact R P C q) z
        (plusReference R N P C (.inr q))).val
          ((C.canonical q).borel.liftedW⁻¹ *
            (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t
      ∂arithmeticRootMeasure R N (.inr q)) =
    (arithmeticRootScale R (.inr q) : ℂ) *
      forwardFactor (LocalField F q) (integerHaar R N q) z * (reference R P C (.inr q)).val t := by
  have hz' : convergenceHalfPlane .plus z := by
    simpa [convergenceHalfPlane, KPContinuation.spectralDomain, neg_div] using hz
  simp_rw [exterior_parameter_input R N P C q hq]
  rw [arithmeticRootMeasure_eq R N (imageData R N P C) (.inr q)]
  have hi := actualCanonicalContinued_integrable F q R.A.zeta12 R.A.primitive_zeta12
    (C.canonical q) (C.polarization q) (integerHaar R N q) (integerHaar_integer R N q)
    .plus z hz'
    (compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus z (exteriorProfile R N P C q)) 1 t
  refine ⟨hi.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_ofReal (arithmeticRootScale_pos R (.inr q)).le]
  change (arithmeticRootScale R (.inr q) : ℂ) * (∫ x : LocalField F q,
    ((compactTrivialization (C.canonical q).borel (C.polarization q)
      (C.canonical q).iwasawa .plus z (exteriorProfile R N P C q)).val
        ((C.canonical q).borel.liftedW⁻¹ *
          (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t
      ∂integerHaar R N q) = _
  rw [exterior_integer_integral R N P C q hq z hz' t]
  ring

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
