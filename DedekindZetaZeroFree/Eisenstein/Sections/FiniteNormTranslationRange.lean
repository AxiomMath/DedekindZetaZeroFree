module

public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteNormPartition
public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularSymmetriesAndUniformRightLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
namespace DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ}

theorem iwasawaNorm_finite_locallyConstant :
    IsLocallyConstant (fun n : KPGlobalTorusFunctionData.finitePart F ζ hζ =>
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D n.val) := by
  obtain ⟨J, hJ⟩ := KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level D
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (J.toOpenSubgroup : Set _),
    J.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro y hy
    have h := hJ x.val ⟨(x⁻¹ * y).val, ⟨x⁻¹ * y, hy, rfl⟩⟩
    simpa using h

theorem logIncrement_finite_locallyConstant
    (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    IsLocallyConstant (fun k : D.K => logIncrement (D := D) k.val u.val) := by
  have hn : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  let c : D.K → KPGlobalTorusFunctionData.finitePart F ζ hζ := fun k =>
    ⟨k.val * u.val * k.val⁻¹, hn.conj_mem u.val u.property k.val⟩
  have hc : Continuous c :=
    ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.inv).subtype_mk _
  have hl := (iwasawaNorm_finite_locallyConstant (D := D)).comp_continuous hc
  have hl' := hl.comp (fun n : (ℝ≥0)ˣ => Real.log ((n : ℝ≥0) : ℝ))
  convert hl' using 1
  funext k
  let d : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ :=
    ⟨D.K, D.compact, D.decomposition, D.overlap⟩
  have h₁ : KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (k.val * u.val) =
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (c k).val := by
    have h := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_right_compact F ζ hζ d
      (c k).val k
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      ((c k).val * k.val) = KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (c k).val at h
    simpa [c, mul_assoc] using h
  have h₂ : KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D k.val = 1 :=
    KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_compact F ζ hζ d k
  simp [logIncrement, h₁, h₂]

theorem logIncrement_finite_range
    (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    (Set.range (fun g => logIncrement (D := D) g u.val)).Finite :=
  logIncrement_range_finite u.val (logIncrement_finite_locallyConstant u)

theorem logIncrement_finite_global_locallyConstant
    (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    IsLocallyConstant (fun g => logIncrement (D := D) g u.val) := by
  have hn := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_iwasawaNorm_continuous F ζ hζ D
  have hn0 (g : KPMsRationalCompactCrossPairing.G F ζ hζ) :
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  have hc : Continuous (fun g => logIncrement (D := D) g u.val) := by
    exact ((hn.comp (continuous_id.mul continuous_const)).log (fun g => hn0 (g * u.val))).sub
      (hn.log hn0)
  let B := Set.range (fun g => logIncrement (D := D) g u.val)
  letI : Finite B := (logIncrement_finite_range u).to_subtype
  have hb : Continuous (fun g => (⟨logIncrement (D := D) g u.val, Set.mem_range_self g⟩ : B)) :=
    hc.subtype_mk _
  exact ((IsLocallyConstant.iff_continuous _).mpr hb).comp Subtype.val

end DedekindZetaZeroFree.KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition

end
