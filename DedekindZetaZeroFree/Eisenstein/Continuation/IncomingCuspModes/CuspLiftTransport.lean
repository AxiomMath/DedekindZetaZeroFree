module

public import DedekindZetaZeroFree.Eisenstein.Continuation.IncomingCuspModes.Realization
public import DedekindZetaZeroFree.Adeles.Quotients.CuspEnds.ParabolicOverlapRigidity

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators ContDiff

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ}
variable (B : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)

private theorem transport_coveredPoint_base (a : Cusps F ζ hζ C R P H U)
    (ε : rootsOfUnity 3 F) (z : KPCuspCharts.Coordinates F) :
    KPContSectorCoveredQuotientVocabulary.q F ζ hζ (level F ζ hζ C R P H U)
      (coveredPoint F ζ hζ C R P H U a ε z) =
      KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U) R P H a z := by
  have he : coveredPoint F ζ hζ C R P H U a ε z =
      KPContSectorCoveredQuotientVocabulary.z F ζ hζ (level F ζ hζ C R P H U) ε
        (coveredPoint F ζ hζ C R P H U a 1 z) := by
    simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.z_mk, map_one]
  rw [he, KPContSectorCoveredQuotientVocabulary.q_z]
  simp [coveredPoint, KPContSectorCoveredQuotientVocabulary.q_mk, map_one,
    KPContActualCollarBuffer.chartLift, KPContSectorSmoothFramesSupport.cuspPoint,
    KPContFlatCuspIncomingEvaluation.atlas]

private theorem transport_lift_pins
    (x : Covered F ζ hζ C R P H U) (l m : EndLift F ζ hζ C R P H U B x) :
    l.cusp = m.cusp ∧ l.coordinates.2 = m.coordinates.2 := by
  have hl : KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U)
      R P H l.cusp l.coordinates = KPContSectorCoveredQuotientVocabulary.q F ζ hζ
        (level F ζ hζ C R P H U) x := by
    rw [← transport_coveredPoint_base F ζ hζ C R P H U, l.point]
  have hm : KPContActualCollarBuffer.chartLift F ζ hζ (level F ζ hζ C R P H U)
      R P H m.cusp m.coordinates = KPContSectorCoveredQuotientVocabulary.q F ζ hζ
        (level F ζ hζ C R P H U) x := by
    rw [← transport_coveredPoint_base F ζ hζ C R P H U, m.point]
  have hab : l.cusp = m.cusp := by
    by_contra hne
    have hlmem : _ ∈ KPContActualCollarBuffer.chartLift F ζ hζ
        (level F ζ hζ C R P H U) R P H l.cusp '' {z | B.τ < z.2} :=
      ⟨l.coordinates, l.high, rfl⟩
    have hmmem : _ ∈ KPContActualCollarBuffer.chartLift F ζ hζ
        (level F ζ hζ C R P H U) R P H m.cusp '' {z | B.τ < z.2} :=
      ⟨m.coordinates, m.high, rfl⟩
    rw [B.lift_range, hl] at hlmem
    rw [B.lift_range, hm] at hmmem
    exact Set.disjoint_left.mp (B.disjoint_ends hne) hlmem hmmem
  refine ⟨hab, ?_⟩
  have hh := B.height_coordinates l.cusp l.coordinates l.high
  have hh' := B.height_coordinates m.cusp m.coordinates m.high
  rw [hl] at hh
  rw [hm, ← hab] at hh'
  exact hh.symm.trans hh'

private theorem transport_incoming_formula (a : Cusps F ζ hζ C R P H U)
    (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (z : KPCuspCharts.Coordinates F) :
    incomingValue F ζ hζ C R P H U ι a s v z =
      KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s z.2 *
        KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U a
          (KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U a ι s v) := by
  simp only [incomingValue, KPContFlatCuspIncomingEvaluation.incoming_formula F ζ hζ C R P H U a ι s hs v,
    KPContFlatCuspIncomingEvaluation.b_formula, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, KPContFlatCuspIncomingEvaluation.zeroProjection_formula]

private theorem transport_central_comm (ε : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

private theorem transport_component_mem (γ : KPCuspArithmetic.PGL2 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (ε η : rootsOfUnity 3 F) (u : (level F ζ hζ C R P H U).toOpenSubgroup)
    (he : KPCuspGenuineMonodromy.central F ζ hζ η * c =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        (KPCuspGenuineMonodromy.central F ζ hζ ε * c) * u) :
    γ ∈ KPCuspGenuineMonodromy.Component F ζ hζ (level F ζ hζ C R P H U) c := by
  have hz : ∀ e : rootsOfUnity 3 F,
      KPCuspGenuineMonodromy.finiteBase F ζ hζ
        (KPCuspGenuineMonodromy.central F ζ hζ e) = 1 := by
    intro e
    have hk : KPCuspGenuineMonodromy.central F ζ hζ e ∈
        (KPCuspGenuineMonodromy.finiteBase F ζ hζ).ker := by
      rw [← (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.1]
      exact ⟨e, rfl⟩
    exact hk
  have he' := congrArg (KPCuspGenuineMonodromy.finiteBase F ζ hζ) he
  simp only [map_mul, hz, one_mul] at he'
  have hlift : KPCuspGenuineMonodromy.finiteBase F ζ hζ
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) =
      KPFiniteComponents.diagonal F γ :=
    congrArg (fun f : KPCuspArithmetic.PGL2 F →* KPFiniteComponents.FinitePGL2 F => f γ)
      (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1
  rw [hlift] at he'
  change KPFiniteComponents.diagonal F γ ∈
    ((level F ζ hζ C R P H U).toOpenSubgroup.toSubgroup.map
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
      (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ c)).toMonoidHom
  refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ (u⁻¹ :
    (level F ζ hζ C R P H U).toOpenSubgroup), ⟨_, (u⁻¹).property, rfl⟩, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
    ]
  have h := congrArg (fun g : KPFiniteComponents.FinitePGL2 F =>
    g * (KPCuspGenuineMonodromy.finiteBase F ζ hζ (u : KPCuspGenuineMonodromy.FiniteCover F ζ hζ))⁻¹ *
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ c)⁻¹) he'
  simpa [mul_assoc] using h

private theorem transport_sheet_pin (a : Cusps F ζ hζ C R P H U)
    (ε η : rootsOfUnity 3 F) (z w : KPCuspCharts.Coordinates F)
    (hz : B.τ < z.2) (hw : B.τ < w.2)
    (he : coveredPoint F ζ hζ C R P H U a ε z =
      coveredPoint F ζ hζ C R P H U a η w) :
    ∃ (g : KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
      (δ : rootsOfUnity 3 F),
      δ ∈ KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (level F ζ hζ C R P H U) ∧
      η = ε * (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a g)⁻¹ * δ := by
  obtain ⟨γ, u, hx, hc⟩ := Quotient.exact he
  simp only [KPContSectorSmoothFramesSupport.cuspPoint] at hx hc
  let At := KPContFlatCuspIncomingEvaluation.atlas F ζ hζ C R P H U
  let σ := (At.cuspAtlas a.1).representative a.2
  let q := (At.cuspAtlas a.1).cusp a.2
  let Γ := KPContFlatCuspIncomingEvaluation.component F ζ hζ C R P H U a
  let c := At.representative a.1
  have hγ : γ ∈ Γ := transport_component_mem F ζ hζ C R P H U γ c ε η u hc
  let γc : Γ := ⟨γ, hγ⟩
  have hd : 0 < KPCuspLogShape.dimension F := (At.cuspAtlas a.1).geometry a.2 |>.positive_dimension
  have hzt : (At.cuspAtlas a.1).threshold < z.2 :=
    lt_of_le_of_lt (by rw [At.common_threshold]; exact B.chart_threshold_le) hz
  have hwt : (At.cuspAtlas a.1).threshold < w.2 :=
    lt_of_le_of_lt (by rw [At.common_threshold]; exact B.chart_threshold_le) hw
  have hz' : σ • KPCuspCharts.toArch F z ∈
      KPCuspSiegel.highCusp F σ (At.cuspAtlas a.1).threshold := by
    refine ⟨KPCuspCharts.toArch F z, ?_, rfl⟩
    change (At.cuspAtlas a.1).threshold < KPCuspLogShape.meanHeight _ _
    rw [KPCuspCharts.toArch_meanHeight F hd]; exact hzt
  have hw' : γ • (σ • KPCuspCharts.toArch F z) ∈
      KPCuspSiegel.highCusp F σ (At.cuspAtlas a.1).threshold := by
    rw [← hx]
    refine ⟨KPCuspCharts.toArch F w, ?_, rfl⟩
    change (At.cuspAtlas a.1).threshold < KPCuspLogShape.meanHeight _ _
    rw [KPCuspCharts.toArch_meanHeight F hd]; exact hwt
  have hp := KPContGenericEndMapRigidity.actual_high_intersection_of_endMap_injective
    F hd Γ q σ (At.cuspAtlas a.1).threshold ((At.cuspAtlas a.1).end_embedding a.2).injective
    γc (σ • KPCuspCharts.toArch F z) hz' hw'
  let g : KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a :=
    ⟨σ⁻¹ * γ * σ, Subgroup.mem_map.mpr ⟨γ, hp, by
      change σ⁻¹ * γ * (σ⁻¹)⁻¹ = σ⁻¹ * γ * σ
      rw [inv_inv]⟩⟩
  have hg : (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ g : KPCuspArithmetic.PGL2 F) = γ := by
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    change σ * (σ⁻¹ * γ * σ) * σ⁻¹ = γ
    group
  obtain ⟨v, hv⟩ := (At.line a.1).finite_comparison
    (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ g)
  change KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ
    (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ g) * c =
      KPCuspGenuineMonodromy.central F ζ hζ
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a g)⁻¹ * c * v at hv
  rw [hg] at hv
  let β := ε * (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a g)⁻¹
  have hf : KPCuspGenuineMonodromy.central F ζ hζ η * c =
      KPCuspGenuineMonodromy.central F ζ hζ β * c * (v * u) := by
    change KPCuspGenuineMonodromy.central F ζ hζ η * c = _ at hc
    rw [← mul_assoc, ← transport_central_comm F ζ hζ ε, mul_assoc
      (KPCuspGenuineMonodromy.central F ζ hζ ε), hv] at hc
    simpa [β, map_mul, mul_assoc] using hc
  let δ := β⁻¹ * η
  refine ⟨g, δ, ?_, ?_⟩
  · change KPCuspGenuineMonodromy.central F ζ hζ δ ∈ (level F ζ hζ C R P H U).toOpenSubgroup
    have hδ : KPCuspGenuineMonodromy.central F ζ hζ δ = (v * u :
        (level F ζ hζ C R P H U).toOpenSubgroup) := by
      have hh := congrArg (fun d : KPCuspGenuineMonodromy.FiniteCover F ζ hζ =>
        c⁻¹ * (KPCuspGenuineMonodromy.central F ζ hζ β)⁻¹ * d) hf
      have hccomm : (KPCuspGenuineMonodromy.central F ζ hζ β)⁻¹ *
          KPCuspGenuineMonodromy.central F ζ hζ η * c =
          c * ((KPCuspGenuineMonodromy.central F ζ hζ β)⁻¹ *
            KPCuspGenuineMonodromy.central F ζ hζ η) := by
        rw [← map_inv, ← map_mul]
        exact transport_central_comm F ζ hζ (β⁻¹ * η) c
      have hh' : c⁻¹ * ((KPCuspGenuineMonodromy.central F ζ hζ β)⁻¹ *
          KPCuspGenuineMonodromy.central F ζ hζ η * c) =
          (v * u : (level F ζ hζ C R P H U).toOpenSubgroup) := by
        simpa [mul_assoc] using hh
      rw [hccomm, inv_mul_cancel_left] at hh'
      simpa only [δ, map_mul, map_inv] using hh'
    rw [hδ]; exact (v * u).property
  · change η = β * (β⁻¹ * η)
    group

theorem actual_endLift_incoming_transport (s : ℂ)
    (hs : s ∈ KPContinuation.spectralDomain) (v : S)
    (x : Covered F ζ hζ C R P H U)
    (l m : EndLift F ζ hζ C R P H U B x) :
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ l.sheet : ℂ) *
      incomingValue F ζ hζ C R P H U ι l.cusp s v l.coordinates =
    (KPContSectorCoveredQuotientVocabulary.chi F ζ hζ m.sheet : ℂ) *
      incomingValue F ζ hζ C R P H U ι m.cusp s v m.coordinates := by
  obtain ⟨hab, ht⟩ := transport_lift_pins F ζ hζ C R P H U B x l m
  have he := l.point.trans m.point.symm
  rw [← hab] at he
  obtain ⟨g, δ, hδ, hsheet⟩ := transport_sheet_pin F ζ hζ C R P H U B
    l.cusp l.sheet m.sheet l.coordinates m.coordinates l.high m.high he
  let e := KPContFlatCuspIncomingEvaluation.sheetEvaluation F ζ hζ C R P H U l.cusp ι s v
  let a := KPContFlatCuspIncomingEvaluation.projectedScalar F ζ hζ C R P H U l.cusp e
  have hr : (KPCuspGenuineMonodromy.chi F ζ hζ
      (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U l.cusp g)⁻¹ : ℂ) * a = a := by
    have h := KPContFlatCuspIncomingEvaluation.projectedScalar_stabilizer
      F ζ hζ C R P H U l.cusp ι s hs v g⁻¹
    simpa only [map_inv] using h
  have ha : a ∈ KPContFlatCuspIncomingEvaluation.Coefficient F ζ hζ C R P H U :=
    (KPContFlatCuspIncomingEvaluation.zeroProjection F ζ hζ C R P H U l.cusp e).property.1.1 0
  have hd : (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * a = a := ha δ hδ
  rw [← hab, transport_incoming_formula F ζ hζ C R P H U ι l.cusp s hs v,
    transport_incoming_formula F ζ hζ C R P H U ι l.cusp s hs v, ← ht,
    KPContSectorCoveredQuotientVocabulary.chi_coe,
    KPContSectorCoveredQuotientVocabulary.chi_coe, hsheet]
  simp only [map_mul, Units.val_mul]
  change (KPCuspGenuineMonodromy.chi F ζ hζ l.sheet : ℂ) * (_ * a) =
    (((KPCuspGenuineMonodromy.chi F ζ hζ l.sheet : ℂ) *
      (KPCuspGenuineMonodromy.chi F ζ hζ
        (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U l.cusp g)⁻¹ : ℂ)) *
      (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ)) * (_ * a)
  calc
    _ = (KPCuspGenuineMonodromy.chi F ζ hζ l.sheet : ℂ) *
        (KPIncomingCasimir.heightFactor (Module.finrank ℚ F / 2) s l.coordinates.2 *
          ((KPCuspGenuineMonodromy.chi F ζ hζ
            (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U l.cusp g)⁻¹ : ℂ) *
            ((KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ) * a))) := by rw [hd, hr]
    _ = _ := by ring

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end
