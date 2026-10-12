module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionMetricAndEigenfunctions
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ArchimedeanGradientEnergy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSectionGradient
open KPContSectorSmoothFramesSupport KPContActualSectorCutoffGraphLimit
open _root_.DedekindZetaZeroFree.KPContThreeL2CotangentHelpers renaming smoothGradient → KPContThreeL2CotangentHelpers.smoothGradient
open _root_.DedekindZetaZeroFree.KPContThreeL2CotangentHelpers renaming arch_coframe_norm → KPContThreeL2CotangentHelpers.arch_coframe_norm
open _root_.DedekindZetaZeroFree.KPContThreeL2CotangentHelpers renaming coframe_reindex → KPContThreeL2CotangentHelpers.coframe_reindex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem gradient_norm_component (Z : smoothSections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    (KPContActualCotangentMeasurableFamilies.normSquare (gradient Z)
      ((H.atlas U).components ⟨i,Quotient.mk _ x⟩) : ℝ) =
      KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
        (Z.val i).val x ^ 2 := by
  have hh := KPContThreeL2CotangentHelpers.smoothGradient_at_arch Z.val Z.property i x
  change (KPContActualCotangentMeasurableFamilies.normSquare (gradient Z)
    ((H.atlas U).components ⟨i,Quotient.mk _ x⟩) : ℝ) = _ at hh
  rw [hh]
  have hr := KPContThreeL2CotangentHelpers.coframe_reindex
    (KPContCotangentActualOverlap.d F) (KPCuspLogShape.dimension F)
    (KPArch.complex_places_of_primitive_twelfth_root F ζ hζ).2.1.symm (Z.val i).val x
  exact hr.trans (KPContThreeL2CotangentHelpers.arch_coframe_norm _ _ (Z.property i) _)
theorem finite_component_eq
    (x : KPCuspGenuineMonodromy.SymmetricSpace F)
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (i : Fin (H.atlas U).componentCount) (γ : KPCuspArithmetic.PGL2 F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c =
      KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i * u) :
    (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x,c)) =
      (H.atlas U).components ⟨i,Quotient.mk _ (γ • x)⟩ := by
  rw [(H.atlas U).components_formula]
  apply Quotient.sound
  refine ⟨γ,ε⁻¹,u⁻¹,rfl,?_⟩
  have he := KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩
  have hcomm : KPCuspGenuineMonodromy.central F ζ hζ ε *
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε := by
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp he _).symm
  change (H.atlas U).representative i = _
  rw [map_inv]
  have ht : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
      (KPCuspGenuineMonodromy.central F ζ hζ ε)⁻¹ =
      (KPCuspGenuineMonodromy.central F ζ hζ ε)⁻¹ *
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ := by
    exact (Commute.symm hcomm).inv_right.eq
  rw [ht, mul_assoc _ _ c, hc]
  change (H.atlas U).representative i =
    (KPCuspGenuineMonodromy.central F ζ hζ ε)⁻¹ *
      (KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i * u.val) * u.val⁻¹
  group
theorem covariantNorm_unit_mul (n : ℕ) (f : KPArch.Space n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℂ) (hc : ‖c‖ = 1) (x : KPArch.Space n) :
    KPContActualChamberOutgoingAdapter.covariantNorm n 1 (fun y => c * f y) x =
      KPContActualChamberOutgoingAdapter.covariantNorm n 1 f x := by
  unfold KPContActualChamberOutgoingAdapter.covariantNorm
  simp only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  have hd : KPContActualChamberOutgoingAdapter.frameDerivative n v (fun y => c*f y) x =
      c * KPContActualChamberOutgoingAdapter.frameDerivative n v f x := by
    unfold KPContActualChamberOutgoingAdapter.frameDerivative
    rw [fderiv_const_mul (hf.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hd,norm_mul,hc,one_mul]
theorem finite_slice (Z : smoothSections F ζ hζ U R P H)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPContSectorCoveredQuotientVocabulary.FiniteCover F ζ hζ)
    (i : Fin (H.atlas U).componentCount) (γ : KPCuspArithmetic.PGL2 F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup)
    (hc : KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c =
      KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i * u) :
    ResidualSphericalGeometry.originalScalar F ζ hζ U R P H Z
      (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (Z.val i).val (γ • KPMsFixedHaarDisintegration.archBasepoint F a) := by
  let f := (smoothS F ζ hζ U R P H).symm Z
  have hz : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f.val = Z.val :=
    congrArg Subtype.val ((smoothS F ζ hζ U R P H).apply_symm_apply Z)
  change f.val.val _ = _
  rw [KPContSectorScalarLineAlgebra.group_lift_formula,
    ← (KPContSectorScalarLineAlgebra.J F ζ hζ U f.val).property.1 _ _ γ,
    hc, (KPContSectorScalarLineAlgebra.J F ζ hζ U f.val).property.2.2,
    KPContSectorScalarLineAlgebra.J_apply,
    phase_lift_formula F ζ hζ U R P H, hz]
  rfl
theorem covariantNorm_rational (f : KPCuspGenuineMonodromy.SymmetricSpace F → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (γ : KPCuspArithmetic.PGL2 F)
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1
      (fun y => f (γ • y)) x ^ 2 =
      KPContActualChamberOutgoingAdapter.covariantNorm (KPCuspLogShape.dimension F) 1 f (γ • x)^2 := by
  obtain ⟨A,hA⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  let g := fun j => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F j).embedding A
  have ha (y : KPCuspGenuineMonodromy.SymmetricSpace F) :
      KPArch.productAction (KPCuspLogShape.dimension F) g y = γ • y := by
    change _ = KPCuspSiegel.action F _ y
    rw [←hA,KPCuspSiegel.action_mk]
    rfl
  simpa only [ha] using ResidualSphericalMetric.covariantNorm_pullback
    (KPCuspLogShape.dimension F) f hf g x
def groupEnergy (f : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℝ :=
  ∑ w : NumberField.InfinitePlace F,
    ((‖KPMsGreenFlux.rightDerivative F ζ hζ w 0 f g‖^2 +
      ‖KPMsGreenFlux.rightDerivative F ζ hζ w 1 f g‖^2)/4 +
    (‖KPMsGreenFlux.rightDerivative F ζ hζ w 2 f g‖^2 +
      ‖KPMsGreenFlux.rightDerivative F ζ hζ w 3 f g‖^2 +
      ‖KPMsGreenFlux.rightDerivative F ζ hζ w 4 f g‖^2 +
      ‖KPMsGreenFlux.rightDerivative F ζ hζ w 5 f g‖^2)/2)

theorem gradient_norm_original (Z : smoothSections F ζ hζ U R P H)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    (KPContActualCotangentMeasurableFamilies.normSquare (gradient Z)
      (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U
        (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ U
          (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))) : ℝ) =
    groupEnergy F ζ hζ (ResidualSphericalGeometry.originalScalar F ζ hζ U R P H Z ∘
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) g := by
  obtain ⟨e,he⟩ := KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent.fullCusp_product_splitting F ζ hζ
  obtain ⟨⟨a,c⟩,rfl⟩ := e.surjective g
  obtain ⟨i,γ,ε,u,hc⟩ := KPContActualSphericalRightFieldIdentification.finite_comparison_exists
    F ζ hζ U R P H c
  let f := fun x => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (Z.val i).val (γ • x)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => (Z.val i).val (γ • x)) :=
    (Z.property i).comp (CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F γ)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_const.mul hs
  have hslice (b : KPSmoothActualFlowData.GInfinity F) :
      (ResidualSphericalGeometry.originalScalar F ζ hζ U R P H Z ∘
        KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) (e (b,c)) =
        f (KPMsFixedHaarDisintegration.archBasepoint F b) := by
    rw [he]
    exact finite_slice F ζ hζ U R P H Z b c i γ ε u hc
  have henergy := ResidualSphericalMetric.original_slice_energy F ζ hζ
    (ResidualSphericalGeometry.originalScalar F ζ hζ U R P H Z ∘
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) e he c f hf hslice a
  change groupEnergy F ζ hζ _ _ = _ at henergy
  rw [henergy]
  dsimp only [f]
  rw [covariantNorm_unit_mul _ _ hs _ (KPContSectorCoveredQuotientVocabulary.chi_norm F ζ hζ ε),
    covariantNorm_rational F _ (Z.property i) γ]
  rw [he, KPContSectorQuotientRelationsComparison.piTilde_quotientMap,
    KPContSectorCoveredQuotientVocabulary.q_mk,
    finite_component_eq F ζ hζ U R P H _ c i γ ε u hc]
  exact gradient_norm_component F ζ hζ U R P H Z i _
end DedekindZetaZeroFree.FourierContinuation.ResidualSectionGradient

end
