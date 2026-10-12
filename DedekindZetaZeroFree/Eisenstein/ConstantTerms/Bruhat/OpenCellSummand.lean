module

public import DedekindZetaZeroFree.Theta.Periods.TranslatedStandardPeriodNonvanishing
public import DedekindZetaZeroFree.Eisenstein.Continuation.Chamber.NormalSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev Cover := KPGlobalTorusFunctionData.G F ζ hζ
abbrev ForwardWeyl := KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPCubicCoverConstruction.adelicW F ζ hζ)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)

theorem scalar_continuous (s : ℂ) (v : S) :
    Continuous (KPContActualSphericalFlatStage.L F ζ hζ U ι s v) := by
  obtain ⟨φ, hφ⟩ := ChamberFlatSource.actual_fixedVector_flat F ζ hζ U ι v
  exact (show Continuous (φ.val s) from (φ.property.1 s).1.1).congr (fun g => hφ s g)

theorem chamber_lift_eq_rational (q : KPChamberBruhatTwoCells.RationalQuotient F) :
    KPContActualChamberNormalSeries.lift F ζ hζ q =
      KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational F ζ hζ
        (Quotient.out q) := by
  unfold KPContActualChamberNormalSeries.lift KPContFlatRationalCosetCovariance.matrixRationalHom
  change KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F
      (Quotient.out q)) = _
  rw [KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_lift]

theorem standard_measurable (s : ℂ) (v : S) (g : Cover F ζ hζ) :
    Measurable (fun x : Adeles F => KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ x * g)) := by
  letI := (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hN := KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous F ζ hζ
  exact ((scalar_continuous F ζ hζ U ι s v).comp
    ((continuous_const.mul hN).mul continuous_const)).measurable

theorem open_cell_term (s : ℂ) (v : S) (g : Cover F ζ hζ)
    (t : F) (x : Adeles F) :
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (KPContActualChamberNormalSeries.lift F ζ hζ (KPChamberBruhatTwoCells.cellIndex F (some t)) *
        (KPGlobalTorusFunctionData.N F ζ hζ x * g)) =
    KPContActualSphericalFlatStage.L F ζ hζ U ι s v
      (ForwardWeyl F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F (Adeles F) t + x) * g) := by
  let v' := KPContFlatSourceRecipe.flatR F ζ hζ s
    (KPContActualSphericalFlatStage.coreInclusion F ζ hζ U ι v)
  change v'.val _ = v'.val _
  rw [chamber_lift_eq_rational]
  change KPChamberBruhatTwoCells.rationalTerm F
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational F ζ hζ)
    v'.val (KPGlobalTorusFunctionData.N F ζ hζ x * g)
    (KPChamberBruhatTwoCells.cellIndex F (some t)) = _
  simp only [KPChamberBruhatTwoCells.cellIndex]
  rw [KPChamberBruhatTwoCells.rationalTerm_eq F _ _
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.scalar_rational_borel_invariant
      F ζ hζ s v')]
  have h := KPChamberBruhatTwoCells.open_cell_translate F
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.rational F ζ hζ)
    (KPGlobalTorusFunctionData.Nhom F ζ hζ)
    (KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.compatible_unipotent F ζ hζ)
    v'.val t x g
  change v'.val (_ * (KPGlobalTorusFunctionData.N F ζ hζ x * g)) = _
  dsimp only [KPGlobalTorusFunctionData.Nhom, MonoidHom.coe_mk, OneHom.coe_mk] at h
  simp only [toAdd_ofAdd] at h
  rw [← mul_assoc, h]
  simpa only [mul_assoc] using
    KPGlobalResidualKernel.RawStageL2.Outgoing.ActualBruhat.section_signed_weyl
      F ζ hζ s v' (KPGlobalTorusFunctionData.N F ζ hζ
        (algebraMap F (Adeles F) t + x) * g)

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
