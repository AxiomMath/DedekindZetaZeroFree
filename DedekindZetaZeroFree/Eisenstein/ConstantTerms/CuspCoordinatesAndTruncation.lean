module

public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightChartJetsAndFlowWords
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.DerivativeWordContinuity

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField Topology ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPMsClearedTruncationL2

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev X := KPSmoothLocalQuotientCharts.X F ζ hζ
abbrev Additive := KPGlobalTorusFunctionData.Adeles F
abbrev AdditiveQuotient := Additive F ⧸ NumberField.AdeleRing.principalSubgroup (NumberField.RingOfIntegers F) F
abbrev Level := KPMsRationalCompactCrossPairing.Level F ζ hζ
abbrev Iwasawa := KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ
abbrev ModelData := KPMsRationalCompactCrossPairing.ModelData F ζ hζ

variable (C : ModelData F ζ hζ) (D : Iwasawa F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (A : KPMsRationalCompactCrossPairing.RawCompactComparison F ζ hζ C D R P H)
variable (U : Level F ζ hζ)

abbrev Stage (T : KPGlobalEisensteinData.CompactTypeStage
    ((KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype)) :=
  KPMsRationalCompactCrossPairing.sourceStage F ζ hζ D U T

def stageToFixedPlus (T) : Stage F ζ hζ D U T →ₗ[ℂ]
    KPMsRationalCompactCrossPairing.fixedPlus F ζ hζ D U := by
  exact { toFun := fun v => ⟨⟨v.val, Submodule.mem_iSup_of_mem U (Submodule.mem_iSup_of_mem T v.property)⟩, by intro g u; obtain ⟨j, hj, heq⟩ := u.property; have hh := v.property.1.2 ⟨j, hj⟩; have h := congrArg (fun f => f.val g) hh; change v.val.val (g * j.val) = v.val.val g at h; change j.val = u.val at heq; rwa [heq] at h⟩, map_add' := by intros; rfl, map_smul' := by intros; rfl }

def smoothSpace : Submodule ℂ (X F ζ hζ → ℂ) where
  carrier := {f | KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f ∧
    (∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (g * u.val)) =
        f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) ∧
    (∀ g (ε : rootsOfUnity 3 F),
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε)) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) *
        f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))}
  zero_mem' := by refine ⟨⟨continuous_const, fun x => contDiff_const⟩, ?_, ?_⟩ <;> simp
  add_mem' := by intro f g hf hg; exact ⟨⟨hf.1.1.add hg.1.1, fun x => (hf.1.2 x).add (hg.1.2 x)⟩, fun x u => congrArg₂ (· + ·) (hf.2.1 x u) (hg.2.1 x u), fun x ε => by change f _ + g _ = _ * (f _ + g _); rw [hf.2.2 x ε, hg.2.2 x ε, mul_add]⟩
  smul_mem' := by intro c f hf; exact ⟨⟨continuous_const.smul hf.1.1, fun x => contDiff_const.smul (hf.1.2 x)⟩, fun x u => congrArg (c • ·) (hf.2.1 x u), fun x ε => by change c * f _ = _ * (c * f _); rw [hf.2.2 x ε]; ring⟩

def smoothDerivatives : List (KPSmoothActualFlowData.B F) →
    smoothSpace F ζ hζ U →ₗ[ℂ] C(X F ζ hζ, ℂ) := fun w =>
  { toFun := fun v =>
      ⟨KPSmoothActualFlowData.wordDerivative F ζ hζ w v.val,
        ActualWordSpatial.word_continuous F ζ hζ U v.val v.property.1 v.property.2.1 w⟩
    map_add' := fun v u => ContinuousMap.ext fun x => congrFun
      (ActualWordLinearity.word_add F ζ hζ v.val u.val v.property.1 u.property.1 w) x
    map_smul' := fun c v => ContinuousMap.ext fun x => congrFun
      (ActualWordLinearity.word_smul F ζ hζ c v.val v.property.1 w) x }

def stageDerivatives (T) : List (KPSmoothActualFlowData.B F) →
    Stage F ζ hζ D U T →ₗ[ℂ] C(G F ζ hζ, ℂ) :=
  NativeStageJets.stageWords F ζ hζ D U T

def rationalLift (γ : Matrix.ProjGenLinGroup (Fin 2) F) : G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ
      (Classical.choose (Matrix.ProjGenLinGroup.mk_surjective γ)))

theorem rationalLift_mk (m : Matrix.GeneralLinearGroup (Fin 2) F) :
    rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk m) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ m) := by let n := Classical.choose (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m)); have hn : Matrix.ProjGenLinGroup.mk n = Matrix.ProjGenLinGroup.mk m := Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective (Matrix.ProjGenLinGroup.mk m)); obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hn; let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp (KPAdelicCoverRestrictedProduct.rationalHom F ζ hζ); have hscalar : φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = 1 := KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨z, rfl⟩; change φ n = φ m; rw [← hz, map_mul, hscalar, mul_one]

def rationalCosetLift (q : KPChamberBruhatTwoCells.RationalQuotient F) : G F ζ hζ :=
  rationalLift F ζ hζ (Quotient.out q)

structure Continuation (T) where
  dx : Measure (Additive F)
  dq : Measure (AdditiveQuotient F)
  additiveHaar : dx.IsAddHaarMeasure
  probability : IsProbabilityMeasure dq
  compatibleHaar : KPChamberAdditivePeriodization.CompatibleHaar F dx dq
  E : ℂ → Stage F ζ hζ D U T →ₗ[ℂ] (X F ζ hζ → ℂ)
  M : ℂ → Stage F ζ hζ D U T →ₗ[ℂ]
    KPMsRationalCompactCrossPairing.fixedMinus F ζ hζ D U
  chamber_summable : ∀ s : ℂ, (1 / 3 : ℝ) < s.re → ∀ v g,
    KPGlobalEisensteinData.EisensteinSummable (rationalCosetLift F ζ hζ)
      (A.sourceFlat s (stageToFixedPlus F ζ hζ D U T v).val).val g
  chamber_agreement : ∀ s : ℂ, ∀ hs : (1 / 3 : ℝ) < s.re, ∀ v g,
    E s v (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      KPGlobalEisensteinData.eisenstein (rationalCosetLift F ζ hζ)
        (A.sourceFlat s (stageToFixedPlus F ζ hζ D U T v).val).val g
        (chamber_summable s hs v g)
  intertwiner_integrable : ∀ s : ℂ, (1 / 3 : ℝ) < s.re → ∀ v g,
    KPGlobalEisensteinData.IntertwinerIntegrable dx
      (rationalLift F ζ hζ
        (KPChamberBruhatTwoCells.rationalWeyl F))
      (KPGlobalTorusFunctionData.N F ζ hζ)
      (A.sourceFlat s (stageToFixedPlus F ζ hζ D U T v).val).val g
  intertwiner_agreement : ∀ s : ℂ, ∀ hs : (1 / 3 : ℝ) < s.re, ∀ v g,
    (A.targetFlat s (M s v).val).val g =
      KPGlobalEisensteinData.intertwiner dx
        (rationalLift F ζ hζ
          (KPChamberBruhatTwoCells.rationalWeyl F))
        (KPGlobalTorusFunctionData.N F ζ hζ)
        (A.sourceFlat s (stageToFixedPlus F ζ hζ D U T v).val).val g
        (intertwiner_integrable s hs v g)
  E_meromorphic : ∀ v x, MeromorphicOn (fun s => E s v x) KPContinuation.spectralDomain
  M_meromorphic : ∀ v g,
    MeromorphicOn (fun s => (A.targetFlat s (M s v).val).val g) KPContinuation.spectralDomain
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : Metric.ball (0 : ℂ) radius ⊆ KPContinuation.spectralDomain
  clearedE : ℂ → Stage F ζ hζ D U T →ₗ[ℂ] smoothSpace F ζ hζ U
  clearedM : ℂ → Stage F ζ hζ D U T →ₗ[ℂ]
    KPMsRationalCompactCrossPairing.fixedMinus F ζ hζ D U
  clearsE : ∀ s ∈ Metric.ball 0 radius, s ≠ 0 → ∀ v, (clearedE s v).val = s • E s v
  clearsM : ∀ s ∈ Metric.ball 0 radius, s ≠ 0 → ∀ v, clearedM s v = s • M s v
  smooth_holomorphic : ∀ f : ℂ → Stage F ζ hζ D U T,
    KPGlobalEisensteinData.SmoothHolomorphicOn (stageDerivatives F ζ hζ D U T) f
      (Metric.ball 0 radius) →
    KPGlobalEisensteinData.SmoothHolomorphicOn (smoothDerivatives F ζ hζ U)
      (fun s => clearedE s (f s)) (Metric.ball 0 radius)
  scattering_holomorphic : ∀ f : ℂ → Stage F ζ hζ D U T,
    KPGlobalEisensteinData.SmoothHolomorphicOn (stageDerivatives F ζ hζ D U T) f
      (Metric.ball 0 radius) → ∀ g,
    AnalyticOnNhd ℂ (fun s => (A.targetFlat s (clearedM s (f s)).val).val g)
      (Metric.ball 0 radius)

variable {F ζ hζ C D R P H A U}
variable {T} (B : Continuation F ζ hζ C D R P H A U T)

def g (f : ℂ → Stage F ζ hζ D U T) (s : ℂ) := B.clearedM s (f s)

abbrev Atlas := H.atlas (A.atlasLevel U)
abbrev Cusp := KPMsFixedHaarDisintegration.CuspIndex (Atlas (A := A) (U := U))

def cuspRepresentative (j : Cusp (A := A) (U := U)) : G F ζ hζ :=
  rationalLift F ζ hζ
    (((Atlas (A := A) (U := U)).cuspAtlas j.1).representative j.2)

def cuspEnd (j : Cusp (A := A) (U := U)) (Y : ℝ) : Set (X F ζ hζ) :=
  (P.projection (A.atlasLevel U)) ⁻¹'
    (KPFiniteCuspAtlas.componentMap F ζ hζ (A.atlasLevel U)
      ((Atlas (A := A) (U := U)).representative j.1) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ (A.atlasLevel U)
          ((Atlas (A := A) (U := U)).representative j.1))
        (((Atlas (A := A) (U := U)).cuspAtlas j.1).representative j.2)
        (KPMsFixedHaarDisintegration.logHeight (F := F) Y))

theorem cuspLift_exists (j : Cusp (A := A) (U := U)) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (Atlas (A := A) (U := U)) Y) (x : X F ζ hζ) (hx : x ∈ cuspEnd j Y) :
    ∃ g : G F ζ hζ,
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g = x ∧
      ∃ (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
        (t : ℝ) (ε : rootsOfUnity 3 F)
        (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
        KPMsFixedHaarDisintegration.archBasepoint F a =
          KPCuspSiegel.action F
            (((Atlas (A := A) (U := U)).cuspAtlas j.1).representative j.2)
            (KPCuspCharts.toArch F (p,t)) ∧
        g = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((Atlas (A := A) (U := U)).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val := by
  obtain ⟨g, hg, hframe⟩ := KPMsActualCuspSource.cusp_lift_exists (H := H) (A.atlasLevel U) (A.level_matching U) j Y x hx
  exact ⟨g, hg, hframe.2⟩

def cuspLift (j : Cusp (A := A) (U := U)) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (Atlas (A := A) (U := U)) Y) (x : X F ζ hζ) : G F ζ hζ :=
  if hx : x ∈ cuspEnd j Y then Classical.choose (cuspLift_exists j Y hY x hx)
    else Quotient.out x

def cuspRadius (j : Cusp (A := A) (U := U)) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (Atlas (A := A) (U := U)) Y) (x : X F ζ hζ) :
    KPMsFixedHaarDisintegration.Radius :=
  ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
    ((cuspRepresentative j)⁻¹ * cuspLift j Y hY x) : ℝ≥0) : ℝ), by exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩

 theorem iwasawaNorm_torus_mul (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (g : G F ζ hζ) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (t.val * g) =
      KPGlobalTorusFunctionData.delta F ζ hζ t *
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g := by
  let D' : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ :=
    ⟨D.K, D.compact, D.decomposition, D.overlap⟩
  have hh := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_borel_mul
    F ζ hζ D' t 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simpa only [hn, mul_one, KPGlobalTorusBorelNormTwistTransport.iwasawaNorm,
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm, D'] using hh

def cuspAngular (j : Cusp (A := A) (U := U)) (Y : ℝ)
    (hY : KPMsFixedHaarDisintegration.AdmissibleCutoff
      (Atlas (A := A) (U := U)) Y) (x : X F ζ hζ) :
    KPMsRationalCompactCrossPairing.NormOne F ζ hζ D :=
  ⟨(KPMsFixedHaarDisintegration.radialSection F ζ hζ
      (H.disintegration (A.atlasLevel U)).radial.slot (cuspRadius j Y hY x))⁻¹ *
    (cuspRepresentative j)⁻¹ * cuspLift j Y hY x, by
    let rad := (H.disintegration (A.atlasLevel U)).radial
    let r := cuspRadius j Y hY x
    let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (KPMsFixedHaarDisintegration.positiveSlots F rad.slot r)
    let g := (cuspRepresentative j)⁻¹ * cuspLift j Y hY x
    have hd : KPGlobalTorusFunctionData.delta F ζ hζ t =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g := by
      apply Units.ext
      apply NNReal.eq
      change ((KPGlobalTorusFunctionData.ideleAbs F
        (KPGlobalTorusFunctionData.p F ζ hζ t) : ℝ≥0) : ℝ) = _
      rw [rad.lift_ratio r]
      exact rad.ell_norm r
    rw [mul_assoc]
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      ((t⁻¹).val * g) = 1
    rw [iwasawaNorm_torus_mul (D := D), map_inv, hd, inv_mul_cancel]⟩

run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← Lean.Meta.getEqnsFor?
    ``DedekindZetaZeroFree.KPMsClearedTruncationL2.cuspAngular
  pure ()

end KPMsClearedTruncationL2
end DedekindZetaZeroFree

end
