module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.ArchimedeanInsertion
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarFiniteLevelTransport
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalLevelKernels
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.RationalBorelCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPContFlatCuspIncomingEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)

abbrev atlasLevel :=
  let _ := C; let _ := R; let _ := P; let _ := H
  EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ U

abbrev atlas := H.atlas (atlasLevel F ζ hζ C R P H U)

abbrev Cusps := Σ i : Fin (atlas F ζ hζ C R P H U).componentCount,
  Fin ((atlas F ζ hζ C R P H U).cuspAtlas i).cuspCount

variable (a : Cusps F ζ hζ C R P H U)

abbrev sigma := ((atlas F ζ hζ C R P H U).cuspAtlas a.1).representative a.2
abbrev component := KPCuspGenuineMonodromy.Component F ζ hζ
  (atlasLevel F ζ hζ C R P H U) ((atlas F ζ hζ C R P H U).representative a.1)
abbrev stabilizer := KPCuspArithmetic.conjugatedStabilizer F
  (component F ζ hζ C R P H U a)
  (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2)
  (sigma F ζ hζ C R P H U a)
abbrev parabolic := ((atlas F ζ hζ C R P H U).cuspAtlas a.1).parabolic a.2
abbrev geometry := ((atlas F ζ hζ C R P H U).cuspAtlas a.1).geometry a.2
abbrev rho := ((atlas F ζ hζ C R P H U).line a.1).rho.comp
  (KPCuspGenuineMonodromy.cuspInclusion F (component F ζ hζ C R P H U a)
    (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2)
    (sigma F ζ hζ C R P H U a))
abbrev monodromy := ((atlas F ζ hζ C R P H U).cuspAtlas a.1).monodromy a.2
abbrev frequencies := ((atlas F ζ hζ C R P H U).cuspAtlas a.1).frequencies a.2
abbrev Coefficient := KPCuspGenuineMonodromy.scalarFiber F ζ hζ
  (atlasLevel F ζ hζ C R P H U)
abbrev KernelTorus := KPCuspGenuineMonodromy.KernelTorus
  (stabilizer F ζ hζ C R P H U a) (parabolic F ζ hζ C R P H U a)
  (rho F ζ hζ C R P H U a)
abbrev ZeroFiber := KPCuspFrequencyGap.constantSections (ζ := ζ) (hζ := hζ)
  (stabilizer F ζ hζ C R P H U a) (parabolic F ζ hζ C R P H U a)
  (rho F ζ hζ C R P H U a) (Coefficient F ζ hζ C R P H U)

def LocalZeroSections : Submodule ℂ
    (KPCuspCharts.Shape F → ZeroFiber F ζ hζ C R P H U a) where
  carrier := {f | ∀ (g : stabilizer F ζ hζ C R P H U a) (b : KPCuspCharts.Shape F),
    f (b + KPCuspLogShape.logarithm F H.totallyComplex
      (parabolic F ζ hζ C R P H U a).E
      (parabolic F ζ hζ C R P H U a).integralUnits
      (Additive.ofMul ((parabolic F ζ hζ C R P H U a).ratio g))) =
        (frequencies F ζ hζ C R P H U a).constantSystem.transport
          ((parabolic F ζ hζ C R P H U a).ratio g) (f b)}
  zero_mem' := by
    intro g b
    simp
  add_mem' := by
    intro f g hf hg
    intro h b
    simp only [Pi.add_apply, map_add, hf h b, hg h b]
  smul_mem' := by
    intro c f hf
    intro g b
    simp only [Pi.smul_apply, map_smul, hf g b]

def finiteRepresentative (ε : rootsOfUnity 3 F) : KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  KPCuspGenuineMonodromy.central F ζ hζ ε *
    KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (sigma F ζ hζ C R P H U a)⁻¹ *
        (atlas F ζ hζ C R P H U).representative a.1

 theorem central_comm (ε : rootsOfUnity 3 F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

theorem atlasLevel_mem_globalLevel
    (u : (atlasLevel F ζ hζ C R P H U).toOpenSubgroup) :
    (u.val : KPGlobalTorusFunctionData.G F ζ hζ) ∈
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
  rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U]
  exact Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩

theorem finiteRepresentative_stabilizer
    (g : stabilizer F ζ hζ C R P H U a) (ε : rootsOfUnity 3 F) :
    ∃ u : (atlasLevel F ζ hζ C R P H U).toOpenSubgroup,
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g *
          finiteRepresentative F ζ hζ C R P H U a ε =
        KPCuspGenuineMonodromy.central F ζ hζ
          (rho F ζ hζ C R P H U a g)⁻¹ *
          finiteRepresentative F ζ hζ C R P H U a ε * u := by
  obtain ⟨u, hu⟩ := ((atlas F ζ hζ C R P H U).line a.1).finite_comparison
    (KPCuspGenuineMonodromy.cuspInclusion F (component F ζ hζ C R P H U a)
      (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2)
      (sigma F ζ hζ C R P H U a) g)
  refine ⟨u, ?_⟩
  rw [KPCuspGenuineMonodromy.cuspInclusion_formula, map_mul, map_mul, map_inv] at hu
  have h := congrArg (fun z =>
    (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (sigma F ζ hζ C R P H U a))⁻¹ * z) hu
  change _ = _ at h
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h
  rw [← central_comm F ζ hζ _
    (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
      (sigma F ζ hζ C R P H U a))⁻¹] at h
  have hh := congrArg (fun z => KPCuspGenuineMonodromy.central F ζ hζ ε * z) h
  simp only [finiteRepresentative, map_inv]
  calc
    _ = KPCuspGenuineMonodromy.central F ζ hζ ε *
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ g *
        (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
          (sigma F ζ hζ C R P H U a))⁻¹ *
        (atlas F ζ hζ C R P H U).representative a.1) := by
      simp only [← mul_assoc]
      rw [← central_comm F ζ hζ ε]
    _ = _ := hh.trans (by
      simp only [← mul_assoc]
      change KPCuspGenuineMonodromy.central F ζ hζ ε *
        KPCuspGenuineMonodromy.central F ζ hζ (rho F ζ hζ C R P H U a g)⁻¹ * _ * _ * _ = _
      rw [central_comm F ζ hζ ε, map_inv])

def reindex : KPChamberBruhatTwoCells.RationalQuotient F ≃
    KPChamberBruhatTwoCells.RationalQuotient F where
  toFun := Quotient.map (fun γ => γ * sigma F ζ hζ C R P H U a) (by
    intro x y hxy
    exact QuotientGroup.rightRel_apply.mpr (by
      have h := QuotientGroup.rightRel_apply.mp hxy
      rw [show (y * sigma F ζ hζ C R P H U a) * (x * sigma F ζ hζ C R P H U a)⁻¹
        = y * x⁻¹ from by group]
      exact h))
  invFun := Quotient.map (fun γ => γ * (sigma F ζ hζ C R P H U a)⁻¹) (by
    intro x y hxy
    exact QuotientGroup.rightRel_apply.mpr (by
      have h := QuotientGroup.rightRel_apply.mp hxy
      rw [show (y * (sigma F ζ hζ C R P H U a)⁻¹)
        * (x * (sigma F ζ hζ C R P H U a)⁻¹)⁻¹ = y * x⁻¹ from by group]
      exact h))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    simp [mul_inv_cancel_right]
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro γ
    simp [mul_inv_cancel_left]

theorem reindex_mk (γ : KPCuspArithmetic.PGL2 F) :
    reindex F ζ hζ C R P H U a (KPChamberBruhatTwoCells.rationalCoset F γ) =
      KPChamberBruhatTwoCells.rationalCoset F (γ * sigma F ζ hζ C R P H U a) :=
  rfl

def localGroup (t : ℝ) (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) : KPGlobalTorusFunctionData.G F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
      (KPCuspCharts.toArch F ((x,b),t))) *
    (finiteRepresentative F ζ hζ C R P H U a ε).val

def cuspGroup (t : ℝ) (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F)
    (ε : rootsOfUnity 3 F) : KPGlobalTorusFunctionData.G F ζ hζ :=
  KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ
    (sigma F ζ hζ C R P H U a) * localGroup F ζ hζ C R P H U a t x b ε

variable {S : Type*} [AddCommGroup S] [Module ℂ S]
variable (ι : S →ₗ[ℂ] KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U)

def sheetEvaluation (s : ℂ) : S →ₗ[ℂ] (rootsOfUnity 3 F → ℂ) where
  toFun v ε := KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
    (finiteRepresentative F ζ hζ C R P H U a ε).val
  map_add' := by
    intro v w
    funext ε
    simp only [Pi.add_apply]
    exact congr_fun (map_add (KPContFlatCommonLevelKernel.L F ζ hζ U ι s) v w) _
  map_smul' := by
    intro c v
    funext ε
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congr_fun (map_smul (KPContFlatCommonLevelKernel.L F ζ hζ U ι s) c v) _

theorem sheetEvaluation_formula (s : ℂ) (v : S) (ε : rootsOfUnity 3 F) :
    sheetEvaluation F ζ hζ C R P H U a ι s v ε =
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
        (finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ)) *
          sheetEvaluation F ζ hζ C R P H U a ι 0 v ε := by
  simp only [sheetEvaluation, KPContFlatCommonLevelKernel.L_formula]
  simp

theorem sheetEvaluation_phase (s : ℂ) (v : S) (ε η : rootsOfUnity 3 F) :
    sheetEvaluation F ζ hζ C R P H U a ι s v (ε * η) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        sheetEvaluation F ζ hζ C R P H U a ι s v η := by
  have hrepr : finiteRepresentative F ζ hζ C R P H U a (ε * η) =
      KPCuspGenuineMonodromy.central F ζ hζ ε *
        finiteRepresentative F ζ hζ C R P H U a η := by
    simp only [finiteRepresentative, map_mul, mul_assoc]
  show KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
      (finiteRepresentative F ζ hζ C R P H U a (ε * η)).val = _
  rw [hrepr, Subgroup.coe_mul]
  show KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε *
        (finiteRepresentative F ζ hζ C R P H U a η).val) =
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val
        (finiteRepresentative F ζ hζ C R P H U a η).val
  rw [KPContFlatRationalCosetCovariance.L_centre,
    KPContSectorCoveredQuotientVocabulary.chi_coe]

def identitySheet (s : ℂ) (v : S) (t : ℝ) (x : KPCuspCharts.Horizontal F)
    (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) : ℂ :=
  KPContFlatRationalCosetCovariance.rationalTerm F ζ hζ s (ι v).val
    (cuspGroup F ζ hζ C R P H U a t x b ε)
    (KPContFlatRationalCosetCovariance.cosetEquiv F ζ hζ
      ((reindex F ζ hζ C R P H U a).symm
        (KPChamberBruhatTwoCells.rationalCoset F 1)))

theorem identitySheet_reindexed (s : ℂ) (v : S) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    identitySheet F ζ hζ C R P H U a ι s v t x b ε =
      KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
        (localGroup F ζ hζ C R P H U a t x b ε) := by
  have hsymm : (reindex F ζ hζ C R P H U a).symm
        (KPChamberBruhatTwoCells.rationalCoset F 1) =
      KPChamberBruhatTwoCells.rationalCoset F (sigma F ζ hζ C R P H U a)⁻¹ := by
    apply (reindex F ζ hζ C R P H U a).injective
    rw [Equiv.apply_symm_apply, reindex_mk]
    simp
  have hB : KPChamberBruhatTwoCells.ScalarRationalBorelInvariant F
      (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ)
      (KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val) := by
    intro bb g
    have hmem : (bb : Matrix.ProjGenLinGroup (Fin 2) F) ∈
        (KPGlobalResidualKernel.rationalBorel F ζ hζ).comap
          (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).toMonoidHom := by
      rw [KPContFlatRationalCosetCovariance.rationalBorel_eq F ζ hζ]
      exact bb.property
    have hb : KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F bb ∈
        KPGlobalResidualKernel.rationalBorel F ζ hζ := Subgroup.mem_comap.mp hmem
    show KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val
        (KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
          (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F bb) * g) = _
    exact KPContFlatRationalCosetCovariance.L_rationalBorel F ζ hζ s (ι v).val ⟨_, hb⟩ g
  show KPContFlatRationalCosetCovariance.rationalTerm F ζ hζ s (ι v).val
      (cuspGroup F ζ hζ C R P H U a t x b ε)
      (KPContFlatRationalCosetCovariance.cosetEquiv F ζ hζ
        ((reindex F ζ hζ C R P H U a).symm
          (KPChamberBruhatTwoCells.rationalCoset F 1))) = _
  rw [hsymm, KPContFlatRationalCosetCovariance.rationalTerm_transport]
  rw [KPChamberBruhatTwoCells.rationalTerm_eq F
    (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ)
    (KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val) hB
    (cuspGroup F ζ hζ C R P H U a t x b ε) (sigma F ζ hζ C R P H U a)⁻¹]
  show KPContFlatRationalCosetCovariance.L F ζ hζ s (ι v).val
      (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ
        (sigma F ζ hζ C R P H U a)⁻¹ * cuspGroup F ζ hζ C R P H U a t x b ε) = _
  rw [show KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ
        (sigma F ζ hζ C R P H U a)⁻¹ * cuspGroup F ζ hζ C R P H U a t x b ε =
      localGroup F ζ hζ C R P H U a t x b ε from by
    rw [cuspGroup, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]]
  rfl

theorem flatR_unipotent_left (s : ℂ)
    (f : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (x : KPGlobalTorusFunctionData.Adeles F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (KPContFlatSourceRecipe.flatR F ζ hζ s f).val
      (KPGlobalTorusFunctionData.N F ζ hζ x * g) =
      (KPContFlatSourceRecipe.flatR F ζ hζ s f).val g := by
  have h := (KPContFlatSourceRecipe.flatR F ζ hζ s f).property
    (⟨1, Subgroup.one_mem _⟩ :
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H) x g
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ
      (1 : KPGlobalTorusFunctionData.E F ζ hζ) = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, KPGlobalTorusFunctionData.delta]
  have hc : (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character
      (⟨1, Subgroup.one_mem _⟩ :
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H) : ℂˣ) : ℂ) = 1 := by
    rw [show (((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).character
      (⟨1, Subgroup.one_mem _⟩ :
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H) : ℂˣ)) = 1
        from map_one _]
    rfl
  rw [show (⟨1, Subgroup.one_mem _⟩ :
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ s).H).val =
      (1 : KPGlobalTorusFunctionData.E F ζ hζ) from rfl] at h
  rw [hd, hc, one_mul, one_mul] at h
  simpa using h

theorem identitySheet_height [FiniteDimensional ℂ S]
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S) (t : ℝ)
    (x : KPCuspCharts.Horizontal F) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F) :
    identitySheet F ζ hζ C R P H U a ι s v t x b ε =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t *
        sheetEvaluation F ζ hζ C R P H U a ι s v ε := by
  rw [identitySheet_reindexed F ζ hζ C R P H U a ι s v t x b ε]
  set fv : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) := (ι v).val with hfv
  have hL : ∀ g : KPGlobalTorusFunctionData.G F ζ hζ,
      KPContFlatCommonLevelKernel.L F ζ hζ U ι s v g =
        (KPContFlatSourceRecipe.flatR F ζ hζ s fv).val g := by
    intro g
    rw [KPContFlatCommonLevelKernel.L_formula, KPContFlatSourceRecipe.flatR_formula]
  rw [show KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
      (localGroup F ζ hζ C R P H U a t x b ε) =
        (KPContFlatSourceRecipe.flatR F ζ hζ s fv).val
          (localGroup F ζ hζ C R P H U a t x b ε) from hL _]
  rw [show sheetEvaluation F ζ hζ C R P H U a ι s v ε =
      (KPContFlatSourceRecipe.flatR F ζ hζ s fv).val
        (finiteRepresentative F ζ hζ C R P H U a ε).val from by
    show KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
        (finiteRepresentative F ζ hζ C R P H U a ε).val = _
    exact hL _]
  rw [localGroup]
  rw [KPContinuation.ChamberFlatCasimir.iwasawa_insertion]
  rw [mul_assoc]
  rw [flatR_unipotent_left F ζ hζ s fv
    (KPContinuation.ChamberFlatCasimir.horizontalAdele F ζ hζ
      (KPCuspCharts.toArch F ((x, b), t)), 0)
    ((KPContFlatArchDiagonalMultiplier.aInfinity F ζ hζ
      (KPContinuation.ChamberFlatCasimir.heights F ζ hζ
        (KPCuspCharts.toArch F ((x, b), t)))).val *
      (finiteRepresentative F ζ hζ C R P H U a ε).val)]
  have hheights : KPContinuation.ChamberFlatCasimir.heights F ζ hζ
        (KPCuspCharts.toArch F ((x, b), t)) =
      (fun w => t + (b : Fin (KPCuspLogShape.dimension F) → ℝ)
        (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)) := by
    funext w
    simp [KPContinuation.ChamberFlatCasimir.heights, KPCuspCharts.toArch]
  rw [hheights]
  have hb' : (∑ v : NumberField.InfinitePlace F,
      (b : Fin (KPCuspLogShape.dimension F) → ℝ)
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ v)) = 0 := by
    rw [Equiv.sum_comp (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ)]
    simpa [KPCuspLogShape.sumCoordinates, KPCuspLogShape.hyperplane] using b.property
  rw [KPContFlatArchDiagonalMultiplier.flatR_mean_height F ζ hζ s t
    (fun w => (b : Fin (KPCuspLogShape.dimension F) → ℝ)
      (KPContSectorArchSphericalFibers.infinitePlaceEquiv F ζ hζ w)) hb' fv
    (finiteRepresentative F ζ hζ C R P H U a ε).val]

private theorem rationalLift_eq_matrixRationalHom (γ : KPCuspArithmetic.PGL2 F) :
    KPMsClearedTruncationL2.rationalLift F ζ hζ γ =
      KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ γ := by
  induction γ using Matrix.ProjGenLinGroup.induction_on with
  | mk m =>
    simp only [KPContFlatRationalCosetCovariance.matrixRationalHom,
      MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv_mk,
      KPRationalAdelicSplitting.rationalPGLHom_mk, KPMsClearedTruncationL2.rationalLift_mk]
    rfl

private theorem arch_comm_finite (r : KPSmoothActualFlowData.GInfinity F)
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ r) c.val := by
  apply RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ r
    ⟨c.val, RepresentationTheory.ArchFiniteSplitting.arch_kernel_le_finite F ζ hζ ?_⟩
  have hc := c.property
  rw [MonoidHom.mem_ker] at hc ⊢
  obtain ⟨d, hd⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) c.val
  rw [← hd] at hc ⊢
  funext w
  have hw := congrFun hc w
  change Matrix.ProjGenLinGroup.mk
    (KPAdelicCoverRestrictedProduct.matrixEval F (Sum.inl w)
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ d)) = 1 at hw
  have hh := congrArg
    (Matrix.ProjGenLinGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom) hw
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map
    ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
        (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w)))
      (KPAdelicCoverRestrictedProduct.projection F ζ hζ d)) = 1
  simpa only [Matrix.ProjGenLinGroup.map_mk, map_one,
    Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply,
    KPAdelicCoverRestrictedProduct.matrixEval] using hh

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in
private theorem stabilizer_arch_height_zero
    (g : stabilizer F ζ hζ C R P H U a) :
    ∃ x : KPCuspCharts.Horizontal F, ∃ b : KPCuspCharts.Shape F,
      KPMsFixedHaarDisintegration.archBasepoint F (archRational (g : KPCuspArithmetic.PGL2 F)) =
        KPCuspCharts.toArch F ((x,b),0) := by
  obtain ⟨m, hm, hupper⟩ := (parabolic F ζ hζ C R P H U a).upper g g.property
  have h := (geometry F ζ hζ C R P H U a).actual_action g m hm hupper ((0,0),0)
  rw [← archRational_action] at h
  have hz : KPCuspCharts.toArch F (((0 : KPCuspCharts.Horizontal F),
      (0 : KPCuspCharts.Shape F)),0) = fun _ => (0,0) := by
    funext i; simp [KPCuspCharts.toArch]
  rw [hz] at h
  change KPMsFixedHaarDisintegration.archBasepoint F (archRational (g : KPCuspArithmetic.PGL2 F)) = _ at h
  refine ⟨_, _, h⟩

open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability in
private theorem L_stabilizer_arch [FiniteDimensional ℂ S]
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (g : stabilizer F ζ hζ C R P H U a) (ε : rootsOfUnity 3 F) :
    KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (archRational (g : KPCuspArithmetic.PGL2 F)) *
        (finiteRepresentative F ζ hζ C R P H U a ε).val) =
      sheetEvaluation F ζ hζ C R P H U a ι s v ε := by
  obtain ⟨x,b,hb⟩ := stabilizer_arch_height_zero F ζ hζ C R P H U a g
  obtain ⟨k,hk⟩ := (KPContSectorArchSphericalFibers.archBasepoint_eq_iff F
    (KPContSectorArchSphericalFibers.iwasawaSection F ζ hζ
      (KPCuspCharts.toArch F ((x,b),0))) (archRational (g : KPCuspArithmetic.PGL2 F))).mp
        (by rw [KPContSectorArchSphericalFibers.archBasepoint_iwasawaSection, hb])
  rw [hk, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  rw [mul_assoc, (arch_comm_finite F ζ hζ k.val
    (finiteRepresentative F ζ hζ C R P H U a ε)).eq, ← mul_assoc]
  rw [(KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs).2.1 v _ k]
  have hh := identitySheet_height F ζ hζ C R P H U a ι s hs v 0 x b ε
  rw [identitySheet_reindexed] at hh
  simpa only [localGroup, KPIncomingCasimir.heightFactor, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul] using hh

theorem sheetEvaluation_stabilizer [FiniteDimensional ℂ S]
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (g : stabilizer F ζ hζ C R P H U a) (ε : rootsOfUnity 3 F) :
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) *
      sheetEvaluation F ζ hζ C R P H U a ι s v ε =
        sheetEvaluation F ζ hζ C R P H U a ι s v ε := by
  obtain ⟨m, hm, hupper⟩ := (parabolic F ζ hζ C R P H U a).upper g g.property
  have hgB : (g : KPCuspArithmetic.PGL2 F) ∈ KPChamberBruhatTwoCells.rationalBorel F :=
    Subgroup.mem_map.mpr ⟨m, hupper, hm⟩
  have hgR :
      KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F g ∈
        KPGlobalResidualKernel.rationalBorel F ζ hζ := by
    change (g : KPCuspArithmetic.PGL2 F) ∈
      (KPGlobalResidualKernel.rationalBorel F ζ hζ).comap
        (KPGlobalResidualKernel.RawStageL2.Outgoing.ChamberQuotient.rationalEquiv F).toMonoidHom
    rw [KPContFlatRationalCosetCovariance.rationalBorel_eq]
    exact hgB
  have hrat := KPContFlatRationalCosetCovariance.L_rationalBorel F ζ hζ s (ι v).val
    ⟨_,hgR⟩ (finiteRepresentative F ζ hζ C R P H U a ε).val
  change KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
    (KPContFlatRationalCosetCovariance.matrixRationalHom F ζ hζ g *
      (finiteRepresentative F ζ hζ C R P H U a ε).val) =
    sheetEvaluation F ζ hζ C R P H U a ι s v ε at hrat
  rw [← rationalLift_eq_matrixRationalHom,
    KPContinuation.RationalArchFiniteSplitting.rationalLift_product, mul_assoc] at hrat
  obtain ⟨u,hu⟩ := finiteRepresentative_stabilizer F ζ hζ C R P H U a g ε
  have hu' := congrArg (fun z : KPFiniteCuspAtlas.FiniteCover F ζ hζ => z.val) hu
  simp only [Subgroup.coe_mul] at hu'
  rw [hu', ← mul_assoc,
    (KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs).1 v _
      ⟨u.val, atlasLevel_mem_globalLevel F ζ hζ C R P H U u⟩] at hrat
  rw [← mul_assoc, (arch_comm_finite F ζ hζ _
    (KPCuspGenuineMonodromy.central F ζ hζ (rho F ζ hζ C R P H U a g)⁻¹)).eq,
    mul_assoc] at hrat
  have hc := (KPContFlatCommonLevelKernel.stage_properties F ζ hζ U ι s hs).2.2.1
    v (rho F ζ hζ C R P H U a g)⁻¹
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRational
        (g : KPCuspArithmetic.PGL2 F)) * (finiteRepresentative F ζ hζ C R P H U a ε).val)
  change KPContFlatCommonLevelKernel.L F ζ hζ U ι s v
    ((KPCuspGenuineMonodromy.central F ζ hζ (rho F ζ hζ C R P H U a g)⁻¹).val * _) = _ at hc
  rw [hc, L_stabilizer_arch F ζ hζ C R P H U a ι s hs v g ε] at hrat
  have hh := congrArg (fun z : ℂ =>
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) * z) hrat
  have hchi : (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ
      (rho F ζ hζ C R P H U a g)⁻¹ : ℂ) =
        (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ)⁻¹ := by
    change (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g)⁻¹ : ℂ) = _
    simp only [map_inv, Units.val_inv_eq_inv_val]
  rw [hchi, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul] at hh
  exact hh.symm

abbrev TranslationDeck := (parabolic F ζ hζ C R P H U a).L ⧸
  (KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
    (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)).addSubgroupOf
      (parabolic F ζ hζ C R P H U a).L

def deckCoefficient (q : TranslationDeck F ζ hζ C R P H U a) : ℂ :=
  (KPCuspGenuineMonodromy.chi F ζ hζ
    (rho F ζ hζ C R P H U a
      ((parabolic F ζ hζ C R P H U a).inclusion
        (Multiplicative.ofAdd (Quotient.out q)))) : ℂ)⁻¹

theorem deckCoefficient_mk (x : (parabolic F ζ hζ C R P H U a).L) :
    deckCoefficient F ζ hζ C R P H U a (QuotientAddGroup.mk x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ)⁻¹ := by
  let q : TranslationDeck F ζ hζ C R P H U a := QuotientAddGroup.mk x
  change deckCoefficient F ζ hζ C R P H U a q =
    (KPCuspGenuineMonodromy.chi F ζ hζ
      (rho F ζ hζ C R P H U a
        ((parabolic F ζ hζ C R P H U a).inclusion
          (Multiplicative.ofAdd x))) : ℂ)⁻¹
  have heq : QuotientAddGroup.mk (Quotient.out q) = q := Quotient.out_eq _
  have hmem : -Quotient.out q + x ∈
      (KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
        (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a)).addSubgroupOf
        (parabolic F ζ hζ C R P H U a).L :=
    QuotientAddGroup.leftRel_apply.mp (Quotient.exact heq)
  have hmemK : ((-Quotient.out q + x : (parabolic F ζ hζ C R P H U a).L) : F) ∈
      KPCuspGenuineMonodromy.kernelLattice (stabilizer F ζ hζ C R P H U a)
        (parabolic F ζ hζ C R P H U a) (rho F ζ hζ C R P H U a) :=
    AddSubgroup.mem_addSubgroupOf.mp hmem
  have hker : rho F ζ hζ C R P H U a
      ((parabolic F ζ hζ C R P H U a).inclusion
        (Multiplicative.ofAdd (-Quotient.out q + x))) = 1 := by
    have h := hmemK.2 hmemK.1
    rwa [show (⟨((-Quotient.out q + x : (parabolic F ζ hζ C R P H U a).L) : F), hmemK.1⟩ :
        (parabolic F ζ hζ C R P H U a).L) = -Quotient.out q + x from Subtype.ext rfl] at h
  have hkey : rho F ζ hζ C R P H U a
        ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd x)) =
      rho F ζ hζ C R P H U a
        ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd (Quotient.out q))) := by
    have hx : x = Quotient.out q + (-Quotient.out q + x) := by abel
    rw [hx, ofAdd_add, map_mul, map_mul, hker, mul_one]
  simp only [deckCoefficient, hkey]

private lemma chi_mul_sum_inv {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂˣ) (h : G) :
    (χ h : ℂ) * (∑ g : G, (χ g : ℂ)⁻¹) = ∑ g : G, (χ g : ℂ)⁻¹ := by
  rw [Finset.mul_sum]
  have hbij : ∀ g : G, (χ h : ℂ) * (χ g : ℂ)⁻¹ = (χ (g * h⁻¹) : ℂ)⁻¹ := by
    intro g
    rw [map_mul, Units.val_mul, mul_inv_rev, map_inv, Units.val_inv_eq_inv_val, inv_inv, mul_comm]
  rw [Finset.sum_congr rfl (fun g _ => hbij g)]
  exact Equiv.sum_comp (Equiv.mulRight h⁻¹) (fun g => (χ g : ℂ)⁻¹)

private lemma ofAdd_inv_mul (y z : (parabolic F ζ hζ C R P H U a).L) :
    (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd (y + z)))) : ℂ)⁻¹ =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          (rho F ζ hζ C R P H U a
            ((parabolic F ζ hζ C R P H U a).inclusion
              (Multiplicative.ofAdd z))) : ℂ)⁻¹ *
        (KPCuspGenuineMonodromy.chi F ζ hζ
          (rho F ζ hζ C R P H U a
            ((parabolic F ζ hζ C R P H U a).inclusion
              (Multiplicative.ofAdd y))) : ℂ)⁻¹ := by
  rw [ofAdd_add, map_mul, map_mul, map_mul, Units.val_mul, mul_inv_rev]

private lemma phiC_neg (x : (parabolic F ζ hζ C R P H U a).L) :
    (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd (-x)))) : ℂ)⁻¹ =
      (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) := by
  rw [ofAdd_neg, map_inv, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]

 lemma deck_avg_invariance [Fintype (TranslationDeck F ζ hζ C R P H U a)]
    (x : (parabolic F ζ hζ C R P H U a).L) :
    (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) *
      ((Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q) =
    (Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q := by
  have hT : (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) *
      (∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q) =
      ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q := by
    have hkey : ∀ q : TranslationDeck F ζ hζ C R P H U a,
        deckCoefficient F ζ hζ C R P H U a (q + QuotientAddGroup.mk (-x)) =
          (KPCuspGenuineMonodromy.chi F ζ hζ
            (rho F ζ hζ C R P H U a
              ((parabolic F ζ hζ C R P H U a).inclusion
                (Multiplicative.ofAdd x))) : ℂ) *
          deckCoefficient F ζ hζ C R P H U a q := by
      intro q
      have hq : q + QuotientAddGroup.mk (-x) =
          QuotientAddGroup.mk (Quotient.out q + (-x)) := by
        conv_lhs => rw [← Quotient.out_eq q]
        exact (QuotientAddGroup.mk_add
          ((KPCuspGenuineMonodromy.kernelLattice
            (stabilizer F ζ hζ C R P H U a) (parabolic F ζ hζ C R P H U a)
            (rho F ζ hζ C R P H U a)).addSubgroupOf
              (parabolic F ζ hζ C R P H U a).L) _ _).symm
      rw [hq, deckCoefficient_mk]
      rw [ofAdd_inv_mul, phiC_neg]
      rw [deckCoefficient]
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun q _ => (hkey q).symm)]
    exact Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk (-x)))
      (fun q => deckCoefficient F ζ hζ C R P H U a q)
  calc (KPCuspGenuineMonodromy.chi F ζ hζ
        (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) *
      ((Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q) =
        (Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
          ((KPCuspGenuineMonodromy.chi F ζ hζ
            (rho F ζ hζ C R P H U a
              ((parabolic F ζ hζ C R P H U a).inclusion
                (Multiplicative.ofAdd x))) : ℂ) *
            ∑ q : TranslationDeck F ζ hζ C R P H U a,
              deckCoefficient F ζ hζ C R P H U a q) := by ring
    _ = (Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q := by rw [hT]

 lemma cent_avg_invariance
    [Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U))]
    (ε : rootsOfUnity 3 F)
    (hε : ε ∈ KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) :
    (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      ((Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
        ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U),
          (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹) =
    (Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
      ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
        (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹ := by
  have h := chi_mul_sum_inv
    ((KPCuspGenuineMonodromy.chi F ζ hζ).comp
      (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U)).subtype) ⟨ε, hε⟩
  have h' : (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
        (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹) =
      ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
        (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹ := h
  calc (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      ((Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
        ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U),
          (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹) =
        (Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
          ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
            ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
              (atlasLevel F ζ hζ C R P H U),
              (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹) := by ring
    _ = (Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
      ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U),
        (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹ := by rw [h']

def projectedScalar (e : rootsOfUnity 3 F → ℂ) : ℂ := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  letI := (monodromy F ζ hζ C R P H U a).finite_deck
  letI := Fintype.ofFinite (TranslationDeck F ζ hζ C R P H U a)
  letI := Fintype.ofFinite
    (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U))
  exact ((Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
    ∑ q : TranslationDeck F ζ hζ C R P H U a, deckCoefficient F ζ hζ C R P H U a q) *
    ((Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
      ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U), (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹) *
    ((Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
      ∑ ε : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ * e ε)

def zeroProjection : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ] ZeroFiber F ζ hζ C R P H U a where
  toFun e := ⟨fun _ => projectedScalar F ζ hζ C R P H U a e, by
    refine ⟨?_, fun z => rfl⟩
    refine ⟨fun z => ?_, fun x y => ?_⟩
    · intro ε hε
      letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
      letI : Finite (TranslationDeck F ζ hζ C R P H U a) :=
        (monodromy F ζ hζ C R P H U a).finite_deck
      letI : Fintype (TranslationDeck F ζ hζ C R P H U a) := Fintype.ofFinite _
      letI : Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U)) := Fintype.ofFinite _
      simp only [projectedScalar]
      set A : ℂ := (Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q with hAdef
      set B : ℂ := (Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
        ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U),
          (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹ with hBdef
      set D : ℂ := (Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
        ∑ ε : rootsOfUnity 3 F,
          (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ * e ε with hDdef
      have hB : (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * B = B := by
        rw [hBdef]
        exact cent_avg_invariance F ζ hζ C R P H U ε hε
      rw [show (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * ((A * B) * D) =
        (A * ((KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * B)) * D from by ring, hB]
    · show projectedScalar F ζ hζ C R P H U a e =
        (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) *
        projectedScalar F ζ hζ C R P H U a e
      letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
      letI : Finite (TranslationDeck F ζ hζ C R P H U a) :=
        (monodromy F ζ hζ C R P H U a).finite_deck
      letI : Fintype (TranslationDeck F ζ hζ C R P H U a) := Fintype.ofFinite _
      letI : Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U)) := Fintype.ofFinite _
      simp only [projectedScalar]
      set A : ℂ := (Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
        ∑ q : TranslationDeck F ζ hζ C R P H U a,
          deckCoefficient F ζ hζ C R P H U a q with hAdef
      set B : ℂ := (Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
        ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
          (atlasLevel F ζ hζ C R P H U),
          (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹ with hBdef
      set D : ℂ := (Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
        ∑ ε : rootsOfUnity 3 F,
          (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ * e ε with hDdef
      have hA : (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) * A = A := by
        rw [hAdef]
        exact deck_avg_invariance F ζ hζ C R P H U a x
      rw [show (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) * ((A * B) * D) =
        (((KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
          ((parabolic F ζ hζ C R P H U a).inclusion
            (Multiplicative.ofAdd x))) : ℂ) * A) * B) * D from by ring, hA] ⟩
  map_add' := by
    intro e f
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_add, Pi.add_apply]
    simp only [projectedScalar, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c e
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_smul, Pi.smul_apply]
    letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
    have key : (∑ x : rootsOfUnity 3 F,
          (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)⁻¹ * (c * e x)) =
        c * ∑ x : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)⁻¹ * e x := by
      rw [show (∑ x : rootsOfUnity 3 F,
            (KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)⁻¹ * (c * e x)) =
          ∑ x : rootsOfUnity 3 F, c * ((KPCuspGenuineMonodromy.chi F ζ hζ x : ℂ)⁻¹ * e x) from
        Finset.sum_congr rfl (fun x _ => by ring), ← Finset.mul_sum]
    simp only [projectedScalar, Pi.smul_apply, smul_eq_mul, key, RingHom.id_apply]
    ring

theorem zeroProjection_formula (e : rootsOfUnity 3 F → ℂ)
    (z : KernelTorus F ζ hζ C R P H U a) :
    (zeroProjection F ζ hζ C R P H U a e).val z =
      projectedScalar F ζ hζ C R P H U a e :=
  rfl

theorem projectedScalar_stabilizer [FiniteDimensional ℂ S]
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (g : stabilizer F ζ hζ C R P H U a) :
    (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) *
      projectedScalar F ζ hζ C R P H U a
        (sheetEvaluation F ζ hζ C R P H U a ι s v) =
      projectedScalar F ζ hζ C R P H U a
        (sheetEvaluation F ζ hζ C R P H U a ι s v) := by
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  letI : Finite (TranslationDeck F ζ hζ C R P H U a) :=
    (monodromy F ζ hζ C R P H U a).finite_deck
  letI : Fintype (TranslationDeck F ζ hζ C R P H U a) := Fintype.ofFinite _
  letI : Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
    (atlasLevel F ζ hζ C R P H U)) := Fintype.ofFinite _
  have hsum : (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) *
      (∑ ε : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
        sheetEvaluation F ζ hζ C R P H U a ι s v ε) =
      ∑ ε : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
        sheetEvaluation F ζ hζ C R P H U a ι s v ε := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ε _
    rw [mul_left_comm, sheetEvaluation_stabilizer F ζ hζ C R P H U a ι s hs v g ε]
  let M : ℂ := ((Fintype.card (TranslationDeck F ζ hζ C R P H U a) : ℂ)⁻¹ *
      ∑ q : TranslationDeck F ζ hζ C R P H U a, deckCoefficient F ζ hζ C R P H U a q) *
    ((Fintype.card (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
      (atlasLevel F ζ hζ C R P H U)) : ℂ)⁻¹ *
      ∑ η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ
        (atlasLevel F ζ hζ C R P H U), (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)⁻¹)
  let N : ℂ := ∑ ε : rootsOfUnity 3 F, (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)⁻¹ *
    sheetEvaluation F ζ hζ C R P H U a ι s v ε
  change (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) *
    (M * ((Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ * N)) = M *
      ((Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ * N)
  calc
    _ = M * ((Fintype.card (rootsOfUnity 3 F) : ℂ)⁻¹ *
      ((KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) * N)) := by ring
    _ = _ := by rw [hsum]

def b [FiniteDimensional ℂ S] (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) :
    S →ₗ[ℂ] LocalZeroSections F ζ hζ C R P H U a where
  toFun v := ⟨fun _ => zeroProjection F ζ hζ C R P H U a
    (sheetEvaluation F ζ hζ C R P H U a ι s v), by
      intro g shape
      apply Subtype.ext
      funext z
      rw [(frequencies F ζ hζ C R P H U a).constantSystem.transition_formula g]
      simp only [zeroProjection_formula]
      exact (projectedScalar_stabilizer F ζ hζ C R P H U a ι s hs v g).symm⟩
  map_add' := by
    intro v w
    apply Subtype.ext
    funext shape
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [map_add (sheetEvaluation F ζ hζ C R P H U a ι s) v w, map_add]
  map_smul' := by
    intro c v
    apply Subtype.ext
    funext shape
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [map_smul (sheetEvaluation F ζ hζ C R P H U a ι s) c v, map_smul]
    simp only [RingHom.id_apply]

theorem b_formula [FiniteDimensional ℂ S] (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (shape : KPCuspCharts.Shape F) :
    (b F ζ hζ C R P H U a ι s hs v).val shape =
      zeroProjection F ζ hζ C R P H U a
        (sheetEvaluation F ζ hζ C R P H U a ι s v) :=
  rfl

def W (s : ℂ) (v : S) (t : ℝ) (shape : KPCuspCharts.Shape F) :
    ZeroFiber F ζ hζ C R P H U a :=
  zeroProjection F ζ hζ C R P H U a
    (fun ε => identitySheet F ζ hζ C R P H U a ι s v t 0 shape ε)

theorem incoming_formula [FiniteDimensional ℂ S]
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (t : ℝ) (shape : KPCuspCharts.Shape F) :
    W F ζ hζ C R P H U a ι s v t shape =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t •
        (b F ζ hζ C R P H U a ι s hs v).val shape := by
  rw [b_formula F ζ hζ C R P H U a ι s hs v shape]
  show zeroProjection F ζ hζ C R P H U a
      (fun ε => identitySheet F ζ hζ C R P H U a ι s v t 0 shape ε) = _
  have hfun : (fun ε => identitySheet F ζ hζ C R P H U a ι s v t 0 shape ε) =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s t •
        sheetEvaluation F ζ hζ C R P H U a ι s v := by
    funext ε
    rw [identitySheet_height F ζ hζ C R P H U a ι s hs v t 0 shape ε]
    rfl
  rw [hfun, map_smul]

end DedekindZetaZeroFree.KPContFlatCuspIncomingEvaluation

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
