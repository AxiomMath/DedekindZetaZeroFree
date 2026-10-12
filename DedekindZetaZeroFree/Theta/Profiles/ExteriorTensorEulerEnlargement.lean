module

public import DedekindZetaZeroFree.Eisenstein.Induction.CanonicalExteriorVectorEulerFactors

@[expose] public section

noncomputable section
open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorTensorHaar
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
open KPRankOneShellContinuation KPRankOneShellRepair ActualCofactor
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
variable (E T : Finset (HeightOneSpectrum (𝓞 F))) (hE : C.exceptional ⊆ E) (hET : E ⊆ T)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open _root_.DedekindZetaZeroFree.KPLocalTameIntertwiningBlock renaming compact_extension_value → compact_extension_value
open _root_.DedekindZetaZeroFree.KPAdditiveHaar renaming localNormalizedHaar_eq_addHaar_of_not_mem → localNormalizedHaar_eq_addHaar_of_not_mem
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming compact_forward_eq_integral → compact_forward_eq_integral

def enlargedProfiles
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus) (s : ℂ) (q : T) :=
  if hq : q.val ∈ E then ActualFullCompactTransport.fullCompactProfiles F ζ hζ P C E φ s ⟨q.val,hq⟩
  else FiniteSourceTransport.parameterSource (C.canonical q.val).borel (C.canonical q.val).iwasawa
    (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q.val (C.canonical q.val))
    (C.polarization q.val) .plus
    (ExteriorVectorHaar.canonicalProfile F ζ hζ P C q.val (fun h => hq (hE h))) s

private theorem rationalStageEval_insert
    (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (v : ∀ q : E, KPGlobalTorusFiniteStages.LocalFiber F ζ hζ P C q.val) :
    rationalStageEval F ζ hζ P C T (hE.trans hET) t
      (fun q => if hq : q.val ∈ E then v ⟨q.val,hq⟩
        else KPGlobalTorusFiniteStages.localReference F ζ hζ P C q.val) =
      rationalStageEval F ζ hζ P C E hE t v := by
  have hc := congrArg (fun L => L (PiTensorProduct.tprod ℂ v))
    (KPGlobalTorusFiniteStages.tensor_insertion_compatible F ζ hζ P C E T hE hET)
  simp only [LinearMap.comp_apply, RestrictedTensorSimple.insert_pure] at hc
  unfold rationalStageEval
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
  rw [hc]

theorem actual_finite_euler_enlargement
    (hD : localDifferentSupport F ⊆ (E : Set (HeightOneSpectrum (𝓞 F))))
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (s : ℂ) (hs : convergenceHalfPlane .plus s) :
    (∫ x : ∀ q : T, LocalField F q.val,
      rationalChamberIntegrand F ζ hζ P C T (hE.trans hET)
        (enlargedProfiles F ζ hζ P C E T hE φ s) t s x
      ∂(Measure.pi (fun q : T => localNormalizedHaar F q.val))) =
    KPGlobalFiniteSIntertwiner.enlargementFactor F E T s *
      (∫ x : ∀ q : E, LocalField F q.val,
        rationalChamberIntegrand F ζ hζ P C E hE
          (ActualFullCompactTransport.fullCompactProfiles F ζ hζ P C E φ s) t s x
        ∂(Measure.pi (fun q : E => localNormalizedHaar F q.val))) := by
  have hT := rational_finite_chamber_integral F ζ hζ P C T (hE.trans hET)
    (enlargedProfiles F ζ hζ P C E T hE φ s) t s hs
  have hhead := rational_finite_chamber_integral F ζ hζ P C E hE
    (ActualFullCompactTransport.fullCompactProfiles F ζ hζ P C E φ s) t s hs
  unfold rationalChamberIntegrand
  rw [hT.2, hhead.2]
  let v (q : E) := (localHalfDifferentFactor F q.val : ℂ) •
    (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
      (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
      (unit_mass F q.val) .plus s
      (ActualFullCompactTransport.fullCompactProfiles F ζ hζ P C E φ s q)).val 1
  let c (q : T) : ℂ := if q.val ∈ E then 1 else KPGlobalFiniteSIntertwiner.goodFactor F q.val s
  let w (q : T) := if hq : q.val ∈ E then v ⟨q.val,hq⟩
    else KPGlobalTorusFiniteStages.localReference F ζ hζ P C q.val
  have hv (q : T) : (localHalfDifferentFactor F q.val : ℂ) •
      (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
        (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
        (unit_mass F q.val) .plus s (enlargedProfiles F ζ hζ P C E T hE φ s q)).val 1 =
      c q • w q := by
    by_cases hq : q.val ∈ E
    · simp [enlargedProfiles, c, w, v, hq]
    · apply Subtype.ext
      funext u
      have hdu : q.val ∉ localDifferentSupport F := fun h => hq (hD h)
      have he := (ExteriorVectorHaar.actual_exterior_euler_slot F ζ hζ P C q.val
        (fun h => hq (hE h)) hdu s hs u).2
      change (localHalfDifferentFactor F q.val : ℂ) *
        ((actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
          (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
          (unit_mass F q.val) .plus s (enlargedProfiles F ζ hζ P C E T hE φ s q)).val 1).val u = _
      have hmass : localHalfDifferentFactor F q.val = 1 := by
        have hd0 := localDifferentExponent_eq_zero_of_not_mem F
          (finite_localDifferentSupport F).toFinset (by simp) q.val (by simpa using hdu)
        simp [localHalfDifferentFactor, hd0]
      rw [compact_forward_eq_integral F ζ hζ q.val (C.canonical q.val) (C.polarization q.val)
        (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
        (unit_mass F q.val) (enlargedProfiles F ζ hζ P C E T hE φ s q) 1 u s hs]
      have he' := he
      rw [localNormalizedHaar_eq_addHaar_of_not_mem F q.val hdu] at he'
      simpa only [enlargedProfiles, dite_eq_right hq, c, ite_eq_right hq, w, hmass, Subgroup.coe_one,
        Complex.ofReal_one, one_mul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using he'
  rw [show (fun q : T => (localHalfDifferentFactor F q.val : ℂ) •
    (actualCanonicalContinued F q.val ζ hζ (C.canonical q.val) (C.polarization q.val)
      (Measure.addHaarMeasure (finiteCompletionIntegersPositiveCompacts F q.val))
      (unit_mass F q.val) .plus s (enlargedProfiles F ζ hζ P C E T hE φ s q)).val 1) =
      (fun q => c q • w q) from funext hv,
    MultilinearMap.map_smul_univ, rationalStageEval_insert F ζ hζ P C E T hE hET]
  congr 1
  unfold c KPGlobalFiniteSIntertwiner.enlargementFactor
  rw [Finset.prod_coe_sort_eq_attach]
  rw [Finset.prod_attach T (fun q : HeightOneSpectrum (𝓞 F) => if q ∈ E then (1 : ℂ) else KPGlobalFiniteSIntertwiner.goodFactor F q s)]
  calc
    (∏ q ∈ T, if q ∈ E then (1 : ℂ) else KPGlobalFiniteSIntertwiner.goodFactor F q s) =
        ∏ q ∈ T.filter (fun q => q ∉ E), KPGlobalFiniteSIntertwiner.goodFactor F q s := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q ∈ E <;> simp [hq]
    _ = _ := by congr 1; ext q; simp

theorem unsigned_integer_chamber_mem
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional)
    (x : KPTameCompact.O F q) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (x : KPTameCompact.K F q)) ∈
      (C.canonical q).iwasawa.compact.toOpenSubgroup := by
  obtain ⟨ht, hc⟩ := C.actual_compact q hq
  change _ ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
  rw [hc]
  refine ⟨KPStandardLocalRootLifts.integralW F q * KPStandardLocalRootLifts.integralN F q x, ?_⟩
  rw [map_mul, map_mul, KPStandardLocalRootLifts.W_eq_compact F ζ hζ q ht,
    KPStandardLocalRootLifts.N_eq_compact F ζ hζ q ht x]
  rfl

theorem actual_unsigned_integer_tail
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional)
    (s : ℂ) (x : KPTameCompact.O F q) :
    (compactTrivialization (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus s
      (FiniteSourceTransport.parameterSource (C.canonical q).borel (C.canonical q).iwasawa
        (ActualFullCompactTransport.fullCompactIwasawa F ζ hζ q (C.canonical q))
        (C.polarization q) .plus (ExteriorVectorHaar.canonicalProfile F ζ hζ P C q hq) s)).val
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
            (KPStandardLocalRootLifts.W F ζ hζ (Sum.inr q) *
              KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) (x : KPTameCompact.K F q))) =
      KPGlobalTorusFiniteStages.localReference F ζ hζ P C q := by
  rw [ExteriorVectorHaar.good_parameterSource_extension F ζ hζ P C q hq]
  let k : (C.canonical q).iwasawa.compact.toOpenSubgroup :=
    ⟨_, unsigned_integer_chamber_mem F ζ hζ P C q hq x⟩
  rw [compact_extension_value (LocalField F q) (C.canonical q).borel (C.polarization q)
    (C.canonical q).iwasawa .plus s (ExteriorVectorHaar.canonicalProfile F ζ hζ P C q hq) k]
  rw [KPLocalTameIntertwiningBlock.compact_level_constant (LocalField F q)
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa .plus
    (ExteriorVectorHaar.canonicalProfile F ζ hζ P C q hq)
    ((KPLocalTameIntertwiningBlock.is_spherical_vector_iff (LocalField F q) _ _ _ _ _).mp
      (ExteriorVectorHaar.canonicalProfile_spherical F ζ hζ P C q hq)).1 k]
  exact (KPActualReflectionData.CanonicalPlusReferences.normalized_canonical_section
    (NativeSource.arithmeticData F ζ hζ) P C q hq).choose_spec.2

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ExteriorTensorHaar

end
