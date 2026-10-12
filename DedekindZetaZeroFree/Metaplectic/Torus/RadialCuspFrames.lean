module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CompactCrossRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Kubota.RationalSplitting.ArchimedeanFiniteFactorization
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree.KPBoundedCuspFrames

open scoped Matrix
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}

abbrev Parabolic (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) :=
  KPCuspArithmetic.conjugatedStabilizer F
    (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
    ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)

 def rationalHom : KPCuspArithmetic.PGL2 F →*
    KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
  (QuotientGroup.lift (Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F))
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ)) (by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ)).codRestrict _ (by
    intro g
    induction g using Matrix.ProjGenLinGroup.induction_on with
    | mk G => exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F G, rfl⟩)
 theorem rationalHom_out (g : KPCuspArithmetic.PGL2 F) :
    (rationalHom (ζ := ζ) (hζ := hζ) g).val =
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLQuotient F g.out) := by
  conv_lhs => rw [← Quotient.out_eq g]
  rfl

def actualFiniteRepresentative (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
    ((A.cuspAtlas j.1).representative j.2))⁻¹ * A.representative j.1

def actualCuspLift (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) (p : KPCuspCharts.Cross F)
    (k : KPMsGreenFlux.K F) (r : ℝ) : KPMsGreenFlux.Cover F ζ hζ :=
  KPMsGreenFlux.cuspRepresentative A j *
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r) *
        (actualFiniteRepresentative A j).val

 theorem rationalHom_product (g : KPCuspArithmetic.PGL2 F) :
    (rationalHom (ζ := ζ) (hζ := hζ) g).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding g.out)) *
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g).val := by
  rw [rationalHom_out]
  have hl : KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
      (KPRationalAdelicSplitting.rationalPGLQuotient F g.out) =
      KPMsClearedTruncationL2.rationalLift F ζ hζ g := by
    have hs : g = Matrix.ProjGenLinGroup.mk g.out := (Quotient.out_eq g).symm
    conv_rhs => rw [hs, KPMsClearedTruncationL2.rationalLift_mk]
    rw [KPRationalAdelicSplitting.rationalPGLHom_mk]
    rfl
  rw [hl]
  exact KPContinuation.RationalArchFiniteSplitting.rationalLift_product F ζ hζ g

private theorem insertion_commutes_finite (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val :=
  KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.insertion_commutes_cover
    F ζ hζ a c

theorem actualCuspLift_arch_finite_formula
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) (p : KPCuspCharts.Cross F)
    (k : KPMsGreenFlux.K F) (r : ℝ) :
    actualCuspLift A j p k r = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      ((fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding
        ((A.cuspAtlas j.1).representative j.2).out)) *
          KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r) *
            (A.representative j.1).val := by
  let σ := (A.cuspAtlas j.1).representative j.2
  let a := KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r
  let s := KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ
  have hσ : KPMsGreenFlux.cuspRepresentative A j =
      (rationalHom (ζ := ζ) (hζ := hζ) σ).val := (rationalHom_out σ).symm
  unfold actualCuspLift actualFiniteRepresentative
  rw [hσ, rationalHom_product,
    (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hs := (insertion_commutes_finite (ζ := ζ) (hζ := hζ) a s).symm
  change (_ * s.val) * _ * (s.val⁻¹ * _) = _
  rw [mul_assoc _ s.val _, hs.eq]
  dsimp only [σ, a]
  group

def componentCorrection (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (j : KPMsGreenFlux.Cusps A) : Parabolic A j →*
      KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1) :=
  KPCuspGenuineMonodromy.cuspInclusion F _
    ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in

structure Frames (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (dk : Measure (KPMsGreenFlux.K F)) where
  compactCross : Set (KPCuspCharts.Cross F)
  isCompact_cross : IsCompact compactCross
  bounded : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F → KPCuspCharts.Cross F
  bounded_mem : ∀ j p, bounded j p ∈ compactCross
  gamma : ∀ j : KPMsGreenFlux.Cusps A, KPCuspCharts.Cross F → Parabolic A j
  upperMatrix : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F →
    Matrix.GeneralLinearGroup (Fin 2) F
  upperMatrix_formula : ∀ j p,
    Matrix.ProjGenLinGroup.mk (upperMatrix j p) = (gamma j p : KPCuspArithmetic.PGL2 F)
  upper : ∀ j p, upperMatrix j p 1 0 = 0
  ratio : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F → Fˣ
  ratio_integral : ∀ j p, ratio j p ∈ KPCuspArithmetic.rationalUnits F
  ratio_formula : ∀ j p,
    upperMatrix j p 0 0 = (ratio j p : F) * upperMatrix j p 1 1
  horizontal_formula : ∀ j p i,
    (bounded j p).1 i = (KPCusp.complexPlace F i).embedding (ratio j p : F) * p.1 i +
      (KPCusp.complexPlace F i).embedding (upperMatrix j p 0 1 / upperMatrix j p 1 1)
  rationalCorrection : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F →
    KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ
  rationalCorrection_formula : ∀ j p,
    (rationalCorrection j p).val = KPMsGreenFlux.cuspRepresentative A j *
      KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
        (KPRationalAdelicSplitting.rationalPGLQuotient F (gamma j p).val.out) *
          (KPMsGreenFlux.cuspRepresentative A j)⁻¹
  centralPhase : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F → rootsOfUnity 3 F
  levelCorrection : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F → U.toOpenSubgroup
  finite_correction : ∀ j p,
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (componentCorrection A j (gamma j p)).val *
          A.representative j.1 =
      KPCuspGenuineMonodromy.central F ζ hζ (centralPhase j p) *
        A.representative j.1 * (levelCorrection j p).val
  compactCorrection : KPMsGreenFlux.Cusps A → KPCuspCharts.Cross F → KPMsGreenFlux.K F
  arch_transition : ∀ j p k r,
    (fun w => Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map w.embedding
      (gamma j p : KPCuspArithmetic.PGL2 F).out)) *
        KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ) p k r =
      KPMsGreenFlux.balancedArch (ζ := ζ) (hζ := hζ)
        (bounded j p) (compactCorrection j p * k) r
  transition : ∀ j p k r,
    (rationalCorrection j p).val * actualCuspLift A j p k r =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ (centralPhase j p) *
        actualCuspLift A j (bounded j p) (compactCorrection j p * k) r *
          (levelCorrection j p).val.val
  compact_preserves_haar : ∀ j p,
    MeasurePreserving (fun k => compactCorrection j p * k) dk dk

end DedekindZetaZeroFree.KPBoundedCuspFrames

end
