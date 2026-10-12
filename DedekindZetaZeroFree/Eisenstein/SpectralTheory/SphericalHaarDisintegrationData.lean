module

public import DedekindZetaZeroFree.Adeles.Quotients.SmoothLocalCharts
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AutomorphicHilbertFlows
public import DedekindZetaZeroFree.Adeles.Quotients.CenteredLogarithmicSlot

@[expose] public section

noncomputable section

open scoped Classical NumberField ENNReal NNReal

open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Level := CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)

abbrev Spherical (U : Level F ζ hζ) := KPFiniteCuspAtlas.rawXU F ζ hζ U

instance (U : Level F ζ hζ) : MeasurableSpace (Spherical F ζ hζ U) := borel _

instance (U : Level F ζ hζ) : BorelSpace (Spherical F ζ hζ U) := ⟨rfl⟩

end DedekindZetaZeroFree.KPMsFixedHaar

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ
abbrev X := KPSmoothLocalQuotientCharts.X F ζ hζ

def archBasepoint (g : KPSmoothActualFlowData.GInfinity F) :
    KPFiniteCuspAtlas.SymmetricSpace F := fun i =>
  KPArch.action (g (KPCusp.complexPlace F i)).out (0, 0)

structure SphericalTransport where
  projection : ∀ U : Level F ζ hζ, X F ζ hζ → Spherical F ζ hζ U
  continuous : ∀ U, Continuous (projection U)
  formula : ∀ U (g : KPSmoothActualFlowData.GInfinity F)
      (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ),
    projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ g * c)) =
        Quotient.mk _ (archBasepoint F g, c)
  forget : ∀ (V U : Level F ζ hζ),
    V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup →
      Spherical F ζ hζ V → Spherical F ζ hζ U
  forget_formula : ∀ V U h x c,
    forget V U h (Quotient.mk _ (x,c)) = Quotient.mk _ (x,c)
  forget_continuous : ∀ V U h, Continuous (forget V U h)
  compatible : ∀ V U h x, forget V U h (projection V x) = projection U x

def sphericalMeasure (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ) :
    Measure (Spherical F ζ hζ U) := Measure.map (P.projection U) R.quotientHaar

abbrev Radius := {r : ℝ // 0 < r}

def positiveSlots (w : NumberField.InfinitePlace F) (r : Radius) :
    KPGlobalTorusFunctionData.TorusArch F := fun v =>
  if v = w then (Real.sqrt r.val : ℂ) else 1

def radialSection (w : NumberField.InfinitePlace F) (r : Radius) : Cover F ζ hζ :=
  KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (positiveSlots F w r)

structure RadialData where
  slot : NumberField.InfinitePlace F
  ell : Radius → KPGlobalTorusFunctionData.Ideles F
  continuous_ell : Continuous ell
  ell_one : ell ⟨1, by norm_num⟩ = 1
  ell_mul : ∀ r s : Radius,
    ell ⟨r.val * s.val, mul_pos r.property s.property⟩ = ell r * ell s
  ell_cube : ∀ r, ∃ u : KPGlobalTorusFunctionData.Ideles F, u ^ 3 = ell r
  ell_slots : ∀ r v,
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl v) (ell r : KPAdeles F) =
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ v)).symm (positiveSlots F slot r v)
  ell_finite : ∀ r q,
    KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr q) (ell r : KPAdeles F) = 1
  ell_norm : ∀ r, ((KPGlobalTorusFunctionData.ideleAbs F (ell r) : ℝ≥0) : ℝ) = r.val
  lift_ratio : ∀ r,
    KPGlobalTorusFunctionData.p F ζ hζ
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ (positiveSlots F slot r)) = ell r
  continuous_section : Continuous (radialSection F ζ hζ slot)
  section_one : radialSection F ζ hζ slot ⟨1, by norm_num⟩ = 1
  section_mul : ∀ r s : Radius,
    radialSection F ζ hζ slot ⟨r.val * s.val, mul_pos r.property s.property⟩ =
      radialSection F ζ hζ slot r * radialSection F ζ hζ slot s

def sectionShape (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) (r : Radius) : KPCuspCharts.Shape F :=
  ⟨fun i => (if KPCusp.complexPlace F i = w then Real.log r.val / 2 else 0) -
    Real.log r.val / (2 * (KPCuspLogShape.dimension F : ℝ)), by
    convert single_slot_mean_zero F hF w (Real.log r.val / 2) using 1 <;>
      simp only [div_div, mul_comm]⟩

def radialMeasure : Measure ℝ :=
  volume.withDensity (fun r => ENNReal.ofReal (r ^ 2)⁻¹)

section Atlas
variable {F ζ hζ}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev CuspIndex := Σ i : Fin A.componentCount, Fin (A.cuspAtlas i).cuspCount

abbrev Parabolic (j : CuspIndex A) := (A.cuspAtlas j.1).parabolic j.2
abbrev Geometry (j : CuspIndex A) := (A.cuspAtlas j.1).geometry j.2

abbrev Omega := Σ j : CuspIndex A,
  KPCuspCharts.Base F hF (Parabolic A j).E (Parabolic A j).integralUnits

abbrev CrossSection := Σ j : CuspIndex A,
  KPCuspCharts.CrossQuotient F
    (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))

instance : MeasurableSpace (Omega A) := borel _
instance : BorelSpace (Omega A) := ⟨rfl⟩
instance : MeasurableSpace (CrossSection A) := borel _
instance : BorelSpace (CrossSection A) := ⟨rfl⟩

def angularProjection (x : CrossSection A) : Omega A :=
  ⟨x.1, (Geometry A x.1).atlas.projection x.2⟩

def logHeight (r : ℝ) : ℝ := Real.log r / (2 * (KPCuspLogShape.dimension F : ℝ))

def AdmissibleCutoff (Y : ℝ) : Prop := 0 < Y ∧ A.threshold ≤ logHeight (F := F) Y

def cuspEnds (Y : ℝ) : Set (Spherical F ζ hζ U) :=
  ⋃ j : CuspIndex A,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y)

def probability (β : Measure (Omega A)) : Measure (Omega A) :=
  (β Set.univ)⁻¹ • β

structure FiberKernel where
  unipotent : Omega A → Measure (CrossSection A)
  probability_unipotent : ∀ ω, IsProbabilityMeasure (unipotent ω)
  fiber_support : ∀ ω,
    unipotent ω {x | angularProjection A x = ω} = 1
  measurable_kernel : ∀ E, MeasurableSet E → Measurable (fun ω => unipotent ω E)

  fiber_formula : ∀ j (b : KPCuspCharts.Shape F),
    ∃ dn : Measure (KPCuspCharts.Torus F (Parabolic A j).L),
      dn.IsAddHaarMeasure ∧ IsProbabilityMeasure dn ∧
      unipotent ⟨j, QuotientAddGroup.mk b⟩ =
        Measure.map (fun z => (⟨j, (Geometry A j).atlas.lift (z,b)⟩ : CrossSection A)) dn

structure GeometricDisintegration (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) extends FiberKernel A where
  radial : RadialData F ζ hζ
  beta : Measure (Omega A)
  finite_beta : IsFiniteMeasure beta
  positive_beta : beta Set.univ ≠ 0
  probability_mass : IsProbabilityMeasure (probability A beta)

  componentWeight : Fin A.componentCount → ℝ≥0∞
  positive_componentWeight : ∀ i, 0 < componentWeight i
  finite_componentWeight : ∀ i, componentWeight i < ⊤
  component_measure : ∀ i,
    (sphericalMeasure F ζ hζ R P U).restrict
      (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
    componentWeight i • Measure.map
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
      (KPFiniteCuspAtlas.quotientVolume F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
        (A.cuspAtlas i).fundamentalDomain)
  induced_beta : ∀ E, MeasurableSet E →
    beta E = ∑ j : CuspIndex A,
      (componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
      (Geometry A j).sectionMeasure
        ((fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A)) ⁻¹' E)
  section_disintegration : ∀ f : CrossSection A → ℝ≥0∞, Measurable f →
    (∑ j : CuspIndex A,
      (componentWeight j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
        ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂unipotent ω ∂beta
  modulus : Spherical F ζ hζ U → ℝ
  measurable_modulus : Measurable modulus
  chart : ∀ Y, AdmissibleCutoff A Y →
    CrossSection A × Set.Ioi Y → Spherical F ζ hζ U
  measurable_chart : ∀ Y hY, Measurable (chart Y hY)
  chart_range : ∀ Y hY, Set.range (chart Y hY) = cuspEnds A Y
  chart_embedding : ∀ Y hY, Topology.IsEmbedding (chart Y hY)
  chart_modulus : ∀ Y hY x r, modulus (chart Y hY (x,r)) = r.val

  chart_formula : ∀ Y hY j (p : KPCuspCharts.Cross F) (r : Set.Ioi Y),
    chart Y hY (⟨j, Quotient.mk _ p⟩,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) •
            KPCuspCharts.toArch F
              ((p.1, p.2 + sectionShape F hF radial.slot
                ⟨r.val, lt_trans hY.1 r.property⟩), logHeight (F := F) r.val)))

structure RadialIntegration (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : GeometricDisintegration A R P) : Prop where

  cusp_integral : ∀ Y (hY : AdmissibleCutoff A Y)
      (φ : Spherical F ζ hζ U → ℝ≥0∞), Measurable φ →
    (∫⁻ x in cuspEnds A Y, φ x ∂sphericalMeasure F ζ hζ R P U) =
      D.beta Set.univ *
        ∫⁻ r : Set.Ioi Y, ∫⁻ ω, ∫⁻ x,
          φ (D.chart Y hY (x,r)) ∂D.unipotent ω ∂probability A D.beta
          ∂Measure.comap (Subtype.val : Set.Ioi Y → ℝ) radialMeasure

  shell_coefficient : ∀ Y, AdmissibleCutoff A Y →
    D.beta Set.univ = ENNReal.ofReal (2 * Y) *
      sphericalMeasure F ζ hζ R P U
        (cuspEnds A Y ∩ {x | Y < D.modulus x ∧ D.modulus x ≤ 2 * Y})
  open_positive : (sphericalMeasure F ζ hζ R P U).IsOpenPosMeasure

def kappa (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (D : GeometricDisintegration A R P) : ℝ :=
  (D.beta Set.univ).toReal

end Atlas

structure LevelCompatibility
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) {V U : Level F ζ hζ}
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup)
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (DV : GeometricDisintegration AV R P) (DU : GeometricDisintegration AU R P) where
  cuspForget : CuspIndex AV → CuspIndex AU
  radiusScale : CuspIndex AV → Radius
  angularForget : Omega AV → Omega AU
  measurable_angularForget : Measurable angularForget
  angular_label : ∀ ω, (angularForget ω).1 = cuspForget ω.1
  crossForget : CrossSection AV → CrossSection AU
  measurable_crossForget : Measurable crossForget
  cross_label : ∀ x, (crossForget x).1 = cuspForget x.1
  projection_commutes : ∀ x,
    angularProjection AU (crossForget x) = angularForget (angularProjection AV x)
  induced_angular : Measure.map angularForget
      (DV.beta.withDensity (fun ω => ENNReal.ofReal (radiusScale ω.1).val)) = DU.beta
  induced_probability : Measure.map angularForget
      (probability AV (DV.beta.withDensity
        (fun ω => ENNReal.ofReal (radiusScale ω.1).val))) = probability AU DU.beta
  coefficient : kappa AU R P DU =
    ((DV.beta.withDensity (fun ω => ENNReal.ofReal (radiusScale ω.1).val)) Set.univ).toReal
  common_slot : DV.radial.slot = DU.radial.slot
  chart_commutes : ∀ YV YU (hV : AdmissibleCutoff AV YV) (hU : AdmissibleCutoff AU YU)
      (x : CrossSection AV) (r : Set.Ioi YV)
      (hr : YU < (radiusScale x.1).val * r.val),
    P.forget V U h (DV.chart YV hV (x,r)) =
      DU.chart YU hU (crossForget x, ⟨(radiusScale x.1).val * r.val,hr⟩)
  induced_kernel : ∀ f : CrossSection AU → ℝ≥0∞, Measurable f →
    (∫⁻ ω, ENNReal.ofReal (radiusScale ω.1).val *
      ∫⁻ x, f (crossForget x) ∂DV.unipotent ω ∂DV.beta) =
      ∫⁻ ω, ∫⁻ x, f x ∂DU.unipotent ω ∂DU.beta

structure AllLevels (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) where
  totallyComplex : NumberField.InfinitePlace.nrRealPlaces F = 0
  atlas : ∀ U : Level F ζ hζ, KPFiniteCuspAtlas.Atlas F ζ hζ totallyComplex U
  disintegration : ∀ U, GeometricDisintegration (atlas U) R P
  compatible : ∀ V U h, Nonempty
    (LevelCompatibility F ζ hζ R P h (atlas V) (atlas U)
      (disintegration V) (disintegration U))

end DedekindZetaZeroFree.KPMsFixedHaar

end
end
