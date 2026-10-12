module

public import DedekindZetaZeroFree.Theta.Profiles.NormalizedExteriorReference
public import DedekindZetaZeroFree.Theta.Periods.FiniteHaarIntegralCofactors

@[expose] public section

noncomputable section
open scoped NumberField Classical Matrix
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualFullCompactTransport
open KPLocalPrincipalSeries KPLocalExceptionalConstruction KPLocalStoneVonNeumann
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F)) (S : CanonicalFiniteInducingData F ζ hζ q)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem projection_eq (g : ActualCover F ζ hζ q) :
    S.borel.projection g = KPLocalSmoothRepresentation.projection F ζ hζ q g := by
  induction g using QuotientGroup.induction_on with
  | _ g => exact (S.openCell S.polarization).projection_eq g

theorem canonical_borel_ratio (b : S.borel.B)
    (hb : (b : ActualCover F ζ hζ q) ∈ KPLocalSmoothRepresentation.Borel F ζ hζ q) :
    S.borel.coordinate (S.borel.retract b) = KPRankOneInduction.borelRatio F q
      ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b,hb⟩ := by
  let r := (KPRankOneInduction.borelRatio F q).comp
    ((KPRankOneInduction.borelProjection F q (KPLocalSmoothRepresentation.projection F ζ hζ q)).comp
      { toFun := fun b : S.borel.B => (⟨b.val, by change b.val ∈ actualBorel F ζ hζ q; rw [← S.borel_eq]; exact b.property⟩ : KPLocalSmoothRepresentation.Borel F ζ hζ q)
        map_one' := rfl
        map_mul' := fun _ _ => rfl })
  have ht (t : actualTorus F ζ hζ q) : r (S.borel.torus t) = S.borel.coordinate t := by
    apply Units.ext
    have hp := S.borel.torus_projection t
    rw [projection_eq] at hp
    dsimp only [r,MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _ (KubotaRankTwo.d (LocalField F q) (S.borel.coordinate t) 1) hp.symm]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hn (x : Multiplicative (LocalField F q)) : r (S.borel.upperRoot x) = 1 := by
    apply Units.ext
    have hp := S.borel.upperRoot_projection x
    rw [projection_eq] at hp
    dsimp only [r,MonoidHom.comp_apply]
    rw [KPRankOneInduction.borelRatio_eq F q _ (KubotaRankTwo.n (LocalField F q) x.toAdd) hp.symm]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  change _ = r b
  obtain ⟨x,hx⟩ := S.borel.borel_decomposition b
  conv_rhs => rw [hx,map_mul,ht,hn,mul_one]

theorem exists_full_compact_iwasawa :
    ∃ J : IwasawaData S.borel,
      (J.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
        KPRankOneCartanGeometry.coveredK0 F ζ hζ q := by
  obtain ⟨J,hJ⟩ := ActualFiniteBorel.actual_compact_iwasawa F ζ hζ q
    (ActualFiniteBorel.chartDepth F ζ hζ q) (ActualFiniteBorel.chartDepth_admissible F ζ hζ q)
    S.heisenberg S.borel S.borel_eq (canonical_borel_ratio F ζ hζ q S)
  exact ⟨J,by rw [hJ]; rfl⟩

def fullCompactIwasawa : IwasawaData S.borel :=
  (exists_full_compact_iwasawa F ζ hζ q S).choose

theorem fullCompactIwasawa_compact :
    ((fullCompactIwasawa F ζ hζ q S).compact.toOpenSubgroup :
      Subgroup (ActualCover F ζ hζ q)) = KPRankOneCartanGeometry.coveredK0 F ζ hζ q :=
  (exists_full_compact_iwasawa F ζ hζ q S).choose_spec

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualFullCompactTransport

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.NativeSource
open NumberField
def arithmeticData (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) : SArithmeticData F where
  zeta12 := ζ
  primitive_zeta12 := hζ
  Sf := (Ideal.finite_factors (show Ideal.span ({(6 : 𝓞 F)} : Set (𝓞 F)) ≠ ⊥ from
    Ideal.span_singleton_eq_bot.not.mpr (by norm_num))).toFinset
  S₀ := ∅
  bad_subset := Finset.empty_subset _
  modulus := ⊤
  modulus_ne_zero := top_ne_bot
  above_six := by
    intro q hq
    simpa [Ideal.dvd_span_singleton] using hq
  modulus_support := by
    intro q hq
    exact False.elim (q.isMaximal.ne_top (top_le_iff.mp hq))

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.NativeSource

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualFullCompactTransport
open NumberField KPLocalPrincipalSeries KPLocalExceptionalConstruction
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
variable (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)
variable (E : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
def fullCompactProfiles
    (φ : ∀ q : E, compactPicture (C.canonical q.val).borel (C.polarization q.val)
      (C.canonical q.val).iwasawa .plus) (s : ℂ) (q : E) :=
  FiniteSourceTransport.parameterSource (C.canonical q.val).borel
    (C.canonical q.val).iwasawa (fullCompactIwasawa F ζ hζ q.val (C.canonical q.val))
    (C.polarization q.val) .plus (φ q) s

open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualCofactor renaming actual_arch_trace_spherical_parameter_integral → actual_arch_trace_spherical_parameter_integral

end DedekindZetaZeroFree.KPGlobalResidualConstruction.StandardIntertwinerProducers.NonzeroResidue.ActualFullCompactTransport

end
