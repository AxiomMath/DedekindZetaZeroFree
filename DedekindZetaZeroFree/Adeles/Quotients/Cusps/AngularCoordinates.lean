module

public import DedekindZetaZeroFree.Eisenstein.Induction.BorelModulusAndIwasawaContinuity
public import DedekindZetaZeroFree.Adeles.Quotients.Cusps.CuspFrames

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal
namespace DedekindZetaZeroFree.KPMsActualAngularSource
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
abbrev G := KPGlobalTorusFunctionData.G F ζ hζ
abbrev Level := KPGlobalTorusFunctionData.FiniteLevel F ζ hζ
abbrev Iwasawa := KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ
abbrev NormOne (D : Iwasawa F ζ hζ) :=
  {g : G F ζ hζ // KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g = 1}

def angularRelation (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (g g' : NormOne F ζ hζ D) : Prop :=
  ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val * u.val

def angularSetoid (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (angularRelation F ζ hζ D U)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩

abbrev Omega (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :=
  Quotient (angularSetoid F ζ hζ D U)
instance (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    MeasurableSpace (Omega F ζ hζ D U) := borel _

def fullAngularSetoid (D : Iwasawa F ζ hζ) : Setoid (NormOne F ζ hζ D) where
  r := Relation.EqvGen (fun g g' => ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F),
    g'.val = ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g.val)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h k => Relation.EqvGen.trans _ _ _ h k⟩
abbrev FullOmega (D : Iwasawa F ζ hζ) := Quotient (fullAngularSetoid F ζ hζ D)
instance (D : Iwasawa F ζ hζ) : MeasurableSpace (FullOmega F ζ hζ D) := borel _

def fullToLevel (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    FullOmega F ζ hζ D → Omega F ζ hζ D U := by
  refine Quotient.lift (fun g => Quotient.mk (angularSetoid F ζ hζ D U) g) ?_
  intro a b hab
  apply Quotient.sound
  have hrel : ∀ a b, (fullAngularSetoid F ζ hζ D).r a b →
      (angularSetoid F ζ hζ D U).r a b := by
    apply Relation.EqvGen.mono
    rintro g g' ⟨y, x, h⟩
    exact ⟨y, x, 1, by simpa using h⟩
  exact hrel a b hab

theorem fullToLevel_mk (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (g : NormOne F ζ hζ D) :
    fullToLevel F ζ hζ D U (Quotient.mk _ g) = Quotient.mk _ g := rfl

def angularForget (D : Iwasawa F ζ hζ) (V U : Level F ζ hζ)
    (h : V.toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup) :
    Omega F ζ hζ D V → Omega F ζ hζ D U := by
  apply Quotient.map id
  apply Relation.EqvGen.mono
  rintro g g' ⟨y, x, u, hu⟩
  have hm : KPGlobalTorusFunctionData.globalLevel F ζ hζ V ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono h
  exact ⟨y, x, ⟨u.val, hm u.property⟩, hu⟩

structure SourceRecipe
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where
  iwasawa : Iwasawa F ζ hζ
  atlasLevel : Level F ζ hζ → KPMsFixedHaarDisintegration.Level F ζ hζ
  level_matching : ∀ U, KPGlobalTorusFunctionData.globalLevel F ζ hζ U =
    (atlasLevel U).toOpenSubgroup.toSubgroup.map (KPFiniteCuspAtlas.FiniteCover F ζ hζ).subtype
  height_normalized : ∀ U
    (j : KPMsFixedHaarDisintegration.CuspIndex (H.atlas (atlasLevel U)))
    (a : KPSmoothActualFlowData.GInfinity F) (p : KPCuspCharts.Cross F)
    (t : ℝ) (ε : rootsOfUnity 3 F)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
    KPMsFixedHaarDisintegration.archBasepoint F a =
      KPCuspSiegel.action F (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2)
        (KPCuspCharts.toArch F (p,t)) →
    ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ iwasawa
      ((KPMsActualCuspSource.rationalLift F ζ hζ
        (((H.atlas (atlasLevel U)).cuspAtlas j.1).representative j.2))⁻¹ *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a *
          ((H.atlas (atlasLevel U)).representative j.1).val *
          KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * u.val)) : ℝ≥0) : ℝ) =
      Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t)

def framedRadius (D : Iwasawa F ζ hζ) (σ g : G F ζ hζ) :
    KPMsFixedHaarDisintegration.Radius :=
  ⟨((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) : ℝ≥0) : ℝ),
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))⟩

def framedNormalization (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ g : G F ζ hζ) : G F ζ hζ :=
  (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
    (framedRadius F ζ hζ D σ g))⁻¹ * (σ⁻¹ * g)

theorem framedNormalization_normOne_continuous (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ : G F ζ hζ) :
    (∀ g, KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (framedNormalization F ζ hζ D B σ g) = 1) ∧
    Continuous (framedNormalization F ζ hζ D B σ) := by
  constructor
  · intro g
    let r := framedRadius F ζ hζ D σ g
    let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
      (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
    have hd : KPGlobalTorusFunctionData.delta F ζ hζ t =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (σ⁻¹ * g) := by
      apply Units.ext
      apply NNReal.eq
      change (((KPGlobalTorusFunctionData.ideleAbs F
        (KPGlobalTorusFunctionData.p F ζ hζ t) : ℝ≥0) : ℝ)) = r.val
      rw [B.lift_ratio, B.ell_norm]
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (t⁻¹.val * (σ⁻¹ * g)) = 1
    have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    have he := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul
      F ζ hζ D t⁻¹ 0 (σ⁻¹ * g)
    simpa only [hn, mul_one, map_inv, hd, inv_mul_cancel] using he
  · have hframe : Continuous (fun g : G F ζ hζ => σ⁻¹ * g) :=
      continuous_const.mul continuous_id
    have hr : Continuous (framedRadius F ζ hζ D σ) :=
      ((KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous
        F ζ hζ D).comp hframe).subtype_mk _
    exact ((B.continuous_section.comp hr).inv).mul hframe

section CuspCoordinates
variable {F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (S : SourceRecipe F ζ hζ R P H) (U : Level F ζ hζ)
abbrev Cusp := KPMsFixedHaarDisintegration.CuspIndex (H.atlas (S.atlasLevel U))
abbrev cuspEnd (j : Cusp S U) (Y : ℝ) :=
  KPMsActualCuspSource.cuspEnd (H := H) (S.atlasLevel U) j Y

def cuspRepresentative (j : Cusp S U) : G F ζ hζ :=
  KPMsActualCuspSource.rationalLift F ζ hζ
    (((H.atlas (S.atlasLevel U)).cuspAtlas j.1).representative j.2)

def cuspLift (j : Cusp S U) (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) : G F ζ hζ :=
  if hx : x ∈ cuspEnd S U j Y then
    Classical.choose (KPMsActualCuspSource.cusp_lift_exists
      (H := H) (S.atlasLevel U) (S.level_matching U) j Y x hx)
  else Quotient.out x

theorem cuspLift_frame (j : Cusp S U) (Y : ℝ)
    (x : KPMsActualCuspSource.X F ζ hζ) (hx : x ∈ cuspEnd S U j Y) :
    KPMsActualCuspSource.AdmissibleFrame (H := H) (U := U)
      (S.atlasLevel U) j Y x (cuspLift S U j Y x) := by
  rw [cuspLift, dif_pos hx]
  exact (Classical.choose_spec (KPMsActualCuspSource.cusp_lift_exists
    (H := H) (S.atlasLevel U) (S.level_matching U) j Y x hx)).2

theorem cuspLift_quotient (j : Cusp S U) (Y : ℝ)
    (x : KPMsActualCuspSource.X F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (cuspLift S U j Y x) = x := by
  by_cases hx : x ∈ cuspEnd S U j Y
  · exact (cuspLift_frame S U j Y x hx).1
  · simp only [cuspLift, dif_neg hx]
    exact Quotient.out_eq x

def cuspRadius (j : Cusp S U) (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) :
    KPMsFixedHaarDisintegration.Radius :=
  framedRadius F ζ hζ S.iwasawa (cuspRepresentative S U j) (cuspLift S U j Y x)

theorem cuspRadius_eq_exp (j : Cusp S U) (Y : ℝ)
    (x : KPMsActualCuspSource.X F ζ hζ) (hx : x ∈ cuspEnd S U j Y) :
    ∃ t : ℝ, KPMsFixedHaarDisintegration.logHeight (F := F) Y < t ∧
      (cuspRadius S U j Y x).val = Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t) := by
  obtain ⟨a, p, t, ε, u, ht, ha, he⟩ := (cuspLift_frame S U j Y x hx).2
  refine ⟨t, ht, ?_⟩
  change ((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ S.iwasawa
    ((cuspRepresentative S U j)⁻¹ * cuspLift S U j Y x) : ℝ≥0) : ℝ) = _
  rw [he]
  exact S.height_normalized U j a p t ε u ha

def cuspAngular (j : Cusp S U) (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) :
    NormOne F ζ hζ S.iwasawa :=
  ⟨framedNormalization F ζ hζ S.iwasawa (H.disintegration (S.atlasLevel U)).radial
    (cuspRepresentative S U j) (cuspLift S U j Y x),
    (framedNormalization_normOne_continuous F ζ hζ S.iwasawa
      (H.disintegration (S.atlasLevel U)).radial (cuspRepresentative S U j)).1 _⟩

theorem cuspAngular_formula (j : Cusp S U) (Y : ℝ)
    (x : KPMsActualCuspSource.X F ζ hζ) :
    (cuspAngular S U j Y x).val =
      (KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (S.atlasLevel U)).radial.slot (cuspRadius S U j Y x))⁻¹ *
          (cuspRepresentative S U j)⁻¹ * cuspLift S U j Y x := by
  exact (mul_assoc _ _ _).symm

theorem cuspLift_from_angular (j : Cusp S U) (Y : ℝ)
    (x : KPMsActualCuspSource.X F ζ hζ) :
    cuspLift S U j Y x = cuspRepresentative S U j *
      KPMsFixedHaarDisintegration.radialSection F ζ hζ
        (H.disintegration (S.atlasLevel U)).radial.slot (cuspRadius S U j Y x) *
          (cuspAngular S U j Y x).val := by
  rw [cuspAngular_formula]
  group

def allCuspEnds (Y : ℝ) : Set (KPMsActualCuspSource.X F ζ hζ) :=
  ⋃ j : Cusp S U, cuspEnd S U j Y

def firstCusp (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) : Cusp S U :=
  if h : ∃ j : Cusp S U, x ∈ cuspEnd S U j Y then Classical.choose h
  else
    let i : Fin (H.atlas (S.atlasLevel U)).componentCount :=
      ⟨0, (H.atlas (S.atlasLevel U)).positive_componentCount⟩
    ⟨i, ⟨0, ((H.atlas (S.atlasLevel U)).cuspAtlas i).positive_cuspCount⟩⟩

theorem firstCusp_mem (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ)
    (hx : x ∈ allCuspEnds S U Y) : x ∈ cuspEnd S U (firstCusp S U Y x) Y := by
  have hex : ∃ j : Cusp S U, x ∈ cuspEnd S U j Y := Set.mem_iUnion.mp hx
  simpa only [firstCusp, dif_pos hex] using Classical.choose_spec hex

def fullCoordinates (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) :
    FullOmega F ζ hζ S.iwasawa × ℝ :=
  let j := firstCusp S U Y x
  (Quotient.mk _ (cuspAngular S U j Y x), (cuspRadius S U j Y x).val)

def coordinates (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) :
    Omega F ζ hζ S.iwasawa U × ℝ :=
  let j := firstCusp S U Y x
  (Quotient.mk _ (cuspAngular S U j Y x), (cuspRadius S U j Y x).val)

theorem fullCoordinates_to_level (Y : ℝ) (x : KPMsActualCuspSource.X F ζ hζ) :
    Prod.map (fullToLevel F ζ hζ S.iwasawa U) id (fullCoordinates S U Y x) =
      coordinates S U Y x := rfl
end CuspCoordinates
end DedekindZetaZeroFree.KPMsActualAngularSource

end
