module

public import DedekindZetaZeroFree.Theta.Profiles.SphericalChamberReduction
public import DedekindZetaZeroFree.Metaplectic.Kubota.ArithmeticCompactGenerators
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Iwasawa.NegativeShellCoordinates
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.TameCubicShells
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactModels.ExponentialPolynomialCorrection
public import DedekindZetaZeroFree.Metaplectic.Kubota.FullIntegralCompactIwasawa

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorVectorHaar
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPLocalGoodSphericalImage KPRankOneTameSphericalFactor KPRankOneShellContinuation
open KPLocalTameIntertwiningBlock KPActualReflectionData
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
variable (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open _root_.DedekindZetaZeroFree.KPExceptionalRaw renaming root → root
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming minus_fiber_fixed → minus_fiber_fixed
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming compact_extension_value → compact_extension_value
open _root_.DedekindZetaZeroFree.KPAdditiveHaar renaming localNormalizedHaar_eq_addHaar_of_not_mem → localNormalizedHaar_eq_addHaar_of_not_mem
local notation "S" => C.canonical q
local notation "A₀" => NativeSource.arithmeticData F ζ hζ

def canonicalProfile : compactPicture (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus :=
  (compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus 0).symm
    (CanonicalPlusReferences.normalized_canonical_section A₀ P C q hq).choose

private theorem canonical_reference_spec :
    let f := (CanonicalPlusReferences.normalized_canonical_section A₀ P C q hq).choose
    f ∈ fixedSubmodule (IPlus (C.canonical q).borel (C.polarization q)) (C.canonical q).iwasawa.compact.toOpenSubgroup ∧
      (f.val 1).val 1 = 1 := by
  dsimp only
  exact ⟨(CanonicalPlusReferences.normalized_canonical_section A₀ P C q hq).choose_spec.1,
    (congrArg (fun v : KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q => v.val 1)
      (CanonicalPlusReferences.normalized_canonical_section A₀ P C q hq).choose_spec.2).trans
        (KPGlobalTorusFiniteStages.referenceGoodSpherical F ζ hζ P C q hq).2.1⟩

theorem canonicalProfile_spherical :
    IsSphericalVector (LocalField F q) (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus
      (canonicalProfile F ζ hζ P C q hq) := by
  apply (is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mpr
  refine ⟨?_, ?_⟩
  · apply (compact_level_identification (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus
      (C.canonical q).iwasawa.compact le_rfl 0 _).mpr
    simpa only [canonicalProfile, LinearEquiv.apply_symm_apply] using
      (canonical_reference_spec F ζ hζ P C q hq).1
  · change (((CanonicalPlusReferences.normalized_canonical_section A₀ P C q hq).choose.val
        (1 : ActualCover F ζ hζ q))).val 1 = 1
    exact (canonical_reference_spec F ζ hζ P C q hq).2

theorem canonical_exterior_vector_integral
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (s : ℂ) (hs : convergenceHalfPlane .plus s) :
    ∀ t : actualTorus F ζ hζ q,
      (∫ x : LocalField F q,
        ((compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
          (canonicalProfile F ζ hζ P C q hq)).val
            ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t ∂μ) =
      forwardFactor (LocalField F q) μ s *
        (KPGlobalTorusFiniteStages.localReference F ζ hζ P C q).val t := by
  obtain ⟨ht, hcompact⟩ := C.actual_compact q hq
  obtain ⟨hw, hn⟩ := kernel_generators_mem_of_actual_compact F ζ hζ q S ht hcompact
  have hcoord := negative_shell_iwasawa_coordinate F ζ hζ q S hw hn
  let φp := canonicalProfile F ζ hζ P C q hq
  have hp := canonicalProfile_spherical F ζ hζ P C q hq
  have hz := tame_spherical_zero_shells_of_actual_compact F ζ hζ q S (C.polarization q)
    μ hμ ht hcompact φp hp
  have hc := spherical_scalar_of_cubic_shell_integrals F ζ hζ q (C.canonical q)
    (C.polarization q) μ hμ φp hp
    (fun z _ => spherical_integer_ball_integral (LocalField F q)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa μ φp hp hw hn z)
    (fun z _ n => spherical_shell_integral_deformation (LocalField F q)
      (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa μ φp hcoord hz z n)
  have hW := compact_torus_weyl_stable (LocalField F q) (C.canonical q).borel (C.canonical q).iwasawa hw
  obtain ⟨φm, hm⟩ := exists_minus_spherical_vector (LocalField F q) (C.canonical q).borel
    (C.polarization q) (C.canonical q).iwasawa (C.unramified q hq) hW
  have hch := FourierContinuation.CurrentSphericalReduction.actual_spherical_chamber F ζ hζ q (C.canonical q)
    (C.polarization q) μ hμ (C.unramified q hq) hW φp φm hp hm hc
  intro t
  have hv := hch s hs 1 t
  have hmval : φm.val 1 = KPGlobalTorusFiniteStages.localReference F ζ hζ P C q := by
    exact (KPGlobalTorusFiniteStages.referenceGoodSpherical F ζ hζ P C q hq).2.2 _
      (minus_fiber_fixed (LocalField F q) (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa hW φm
        ((is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mp hm).1)
      ((is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mp hm).2
  have he := compact_extension_value (LocalField F q) (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .minus (-s) φm 1
  simp only [Subgroup.coe_one] at he
  rw [he, hmval] at hv
  exact hv

private theorem completion_residue_card : residueCardinality (LocalField F q) = q.asIdeal.absNorm := by
  let e : q.adicCompletionIntegers F ≃+* (valuation (LocalField F q)).integer := by
    letI : (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have he := (Valuation.isEquiv_iff_valuationSubring _ _).mp
      (ValuativeRel.isEquiv (Valued.v : Valuation (LocalField F q)
        (WithZero (Multiplicative ℤ))) (valuation (LocalField F q)))
    exact RingEquiv.restrict (RingEquiv.refl _) _ _ (fun x => by
      change x ∈ (Valued.v : Valuation (LocalField F q) (WithZero (Multiplicative ℤ))).valuationSubring ↔
        x ∈ (valuation (LocalField F q)).valuationSubring
      rw [he])
  let er := (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField q).trans
    (IsLocalRing.ResidueField.mapEquiv e)
  unfold residueCardinality
  rw [← Nat.card_congr er.toEquiv, Ideal.absNorm_apply]
  rfl

theorem forwardFactor_eq_goodFactor
    (μ : Measure (LocalField F q))
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1) (s : ℂ) :
    forwardFactor (LocalField F q) μ s = KPGlobalFiniteSIntertwiner.goodFactor F q s := by
  have hQ : 0 < (residueCardinality (LocalField F q) : ℝ) := by exact_mod_cast Nat.card_pos
  have he : (residueCardinality (LocalField F q) : ℂ)⁻¹ =
      Complex.exp (-(Real.log (residueCardinality (LocalField F q) : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hQ]
    simp only [Complex.ofReal_natCast]
  unfold forwardFactor forwardFactorInRoot KPRankOneRootParameter.r haarMass
  rw [hμ, ENNReal.toReal_one]
  simp only [Complex.ofReal_one, one_mul]
  rw [he]
  simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold KPGlobalFiniteSIntertwiner.goodFactor KPGlobalGoodEulerFactor.sphericalCoefficient
    KPGlobalFiniteSIntertwiner.residueSize
  rw [completion_residue_card F q]
  simp only [Complex.ofReal_one, one_mul]
  congr 2 <;> congr 1 <;> ring

include hq in

theorem canonical_compact_le_full :
    ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q)).compact.toOpenSubgroup := by
  obtain ⟨ht, hc⟩ := C.actual_compact q hq
  rw [hc, ActualFullCompactTransport.fullCompactIwasawa_compact]
  rintro g ⟨k, rfl⟩
  change KPPGLLocalCover.projection F ζ hζ (Sum.inr q) _ ∈ KPRankOneCartanGeometry.K0 F q
  rw [actualGoodCompactSplit, MonoidHom.comp_apply, KPPGLLocalCover.projection_coverQuotient,
    KPGoodCompactSplitting.projection_kStar]
  exact ⟨k, rfl⟩

include hq in

theorem good_forwardAbs_eq (g : ActualCover F ζ hζ q) :
    LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q)
      (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q)) g =
    LocalCompactChange.forwardAbs F ζ hζ q (C.canonical q) (C.canonical q).iwasawa g := by
  let k := (C.canonical q).iwasawa.compactPart g
  let k' : (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q
      (C.canonical q)).compact.toOpenSubgroup :=
    ⟨k.val, canonical_compact_le_full F ζ hζ P C q hq k.property⟩
  have h := LocalCompactChange.forwardAbs_factorization F ζ hζ q (C.canonical q)
    (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q))
    ((C.canonical q).iwasawa.borelPart g) k'
  rw [← (C.canonical q).iwasawa.decomposition g] at h
  exact h

theorem good_parameterSource_extension (s : ℂ) (g : ActualCover F ζ hζ q) :
    (compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
      (FiniteSourceTransport.parameterSource (C.canonical q).borel (C.canonical q).iwasawa
        (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q))
        (C.polarization q) .plus (canonicalProfile F ζ hζ P C q hq) s)).val g =
    (compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
      (canonicalProfile F ζ hζ P C q hq)).val g := by
  rw [FiniteSourceTransport.parameterSource_extension]
  conv_rhs => rw [FiniteDisplacement.compact_extension_displacement]
  congr 1
  change Complex.exp (s * (Real.log (LocalCompactChange.forwardAbs F ζ hζ q
    (C.canonical q) (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q)) g) : ℂ)) = _
  rw [good_forwardAbs_eq F ζ hζ P C q hq]
  rfl

theorem actual_exterior_euler_slot
    (hD : q ∉ localDifferentSupport F) (s : ℂ) (hs : convergenceHalfPlane .plus s) :
    ∀ t : actualTorus F ζ hζ q,
      Integrable (fun x : LocalField F q =>
        ((compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
          (FiniteSourceTransport.parameterSource (C.canonical q).borel (C.canonical q).iwasawa
            (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q))
            (C.polarization q) .plus (canonicalProfile F ζ hζ P C q hq) s)).val
              ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t)
        (localNormalizedHaar F q) ∧
      (∫ x : LocalField F q,
        ((compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
          (FiniteSourceTransport.parameterSource (C.canonical q).borel (C.canonical q).iwasawa
            (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q))
            (C.polarization q) .plus (canonicalProfile F ζ hζ P C q hq) s)).val
              ((C.canonical q).borel.liftedW⁻¹ * (C.canonical q).borel.upperRoot (Multiplicative.ofAdd x) * 1)).val t
        ∂(localNormalizedHaar F q)) =
          KPGlobalFiniteSIntertwiner.goodFactor F q s *
            (KPGlobalTorusFiniteStages.localReference F ζ hζ P C q).val t := by
  intro t
  simp_rw [good_parameterSource_extension F ζ hζ P C q hq]
  rw [localNormalizedHaar_eq_addHaar_of_not_mem F q hD]
  let μ := Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q)
  have hμ := ActualCofactor.unit_mass F q
  refine ⟨?_, ?_⟩
  · exact KPRankOneShellRepair.actualCanonicalContinued_integrable F q ζ hζ
      (C.canonical q) (C.polarization q) μ hμ .plus s hs
      (compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
        (canonicalProfile F ζ hζ P C q hq)) 1 t
  · rw [canonical_exterior_vector_integral F ζ hζ P C q hq μ hμ s hs t,
      forwardFactor_eq_goodFactor F q μ hμ s]

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorVectorHaar

end
