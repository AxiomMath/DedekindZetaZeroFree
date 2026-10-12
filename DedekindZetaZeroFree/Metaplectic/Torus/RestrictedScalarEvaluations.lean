module

public import DedekindZetaZeroFree.Metaplectic.Torus.LocalPolarizationsAndUnramifiedCharacters
public import DedekindZetaZeroFree.Algebra.TensorProduct.RestrictedTensorSimplicity

@[expose] public section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

structure RawLocalScalarData extends RawLocalFiberData F ζ hζ P T where
  reference : ∀ q, KPLocalStoneVonNeumann.InducedModule (polarization q)
  reference_formula : ∀ q t, (reference q).val t =
    if h : (canonical q).heisenberg.π t ∈ (polarization q).L then
      ((polarization q).ωL ⟨t, h⟩ : ℂ) else 0
  evaluation : ∀ q, KPLocalStoneVonNeumann.InducedModule (polarization q) →
    KPLocalExceptionalConstruction.actualTorus F ζ hζ q → ℂ
  evaluation_formula : ∀ q f t, evaluation q f t =
    f.val t / (Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((canonical q).borel.coordinate t)) (1 / 6 : ℝ) : ℂ)

theorem restricted_local_evaluations_finite_support
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    Function.HasFiniteMulSupport (fun q => C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)) := by
  classical
  have hrfin := Filter.eventually_cofinite.mp raw.eventually
  have hr : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      raw (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ (Sum.inr q) := by
    apply Filter.eventually_cofinite.mpr
    exact hrfin.preimage_embedding ⟨Sum.inr, Sum.inr_injective⟩
  have hb := (KPAdelicCoverRestrictedProduct.bad_finite F).eventually_cofinite_notMem
  have heval : ∀ᶠ q in Filter.cofinite, C.evaluation q
      (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q) = 1 := by
    filter_upwards [hr, hb, S.eventually_cofinite_notMem] with q hraw hbad hq
    have hqe : q ∉ C.exceptional := fun h => hq (hS h)
    obtain ⟨htame, hcompact⟩ := C.actual_compact q hqe
    have hmem : (t q : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
        (C.canonical q).iwasawa.compact.toOpenSubgroup := by
      change (t q : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
        ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup _)
      rw [hcompact]
      change raw (Sum.inr q) ∈ KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q at hraw
      simp only [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hbad] at hraw
      obtain ⟨k, hk⟩ := hraw
      refine ⟨k, ?_⟩
      rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.comp_apply, hk]
      exact (ht q).symm
    let A := (C.canonical q).borel
    let I := (C.canonical q).iwasawa
    have hj : t q ∈ KPLocalGoodSphericalImage.compactTorus A I := by
      change (A.torus (t q) : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
        I.compact.toOpenSubgroup
      rw [(C.canonical q).torus_full]
      exact hmem
    have hu := C.unramified q hqe
    have hpol : (C.canonical q).heisenberg.π (t q) ∈ (C.polarization q).L := by
      rw [← hu.polarization_image]
      exact Subgroup.mem_map.mpr ⟨t q, hj, rfl⟩
    have href : (C.reference q).val (t q) = 1 := by
      rw [C.reference_formula, dif_pos hpol]
      exact congrArg (fun u : ℂˣ => (u : ℂ)) (hu.character_trivial ⟨t q, hj⟩ hpol)
    have hnorm : KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
        (A.coordinate (t q)) = 1 := by
      have h := I.intersection_norm (A.torus (t q)) (by
        rw [(C.canonical q).torus_full]; exact hmem)
      change KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
        (A.coordinate (A.retract (A.torus (t q)))) = 1 at h
      simpa only [A.retract_torus] using h
    have hdenom : (Real.rpow
        (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          (A.coordinate (t q))) (1 / 6 : ℝ) : ℂ) = 1 := by
      have h := congrArg (fun u : ℂˣ => (u : ℂ))
        (ProductPolarization.fullnorm_bridgefinite F q (A.coordinate (t q)))
      simpa [KPGlobalCenterRationalCharacter.positiveComplex,
        KPGlobalCenterRationalCharacter.sixthPower, ActualFiniteTorus.normUnit,
        KPLocalPrincipalSeries.normPower, hnorm, NNReal.coe_rpow] using h
    rw [dif_neg hq, C.evaluation_formula, href]
    rw [show (C.canonical q).borel.coordinate (t q) = A.coordinate (t q) from rfl,
      hdenom, div_one]
  exact Filter.eventually_cofinite.mp heval
end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers
