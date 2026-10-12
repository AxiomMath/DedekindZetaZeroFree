module

public import DedekindZetaZeroFree.Eisenstein.Continuation.MeanZero.ParameterJets
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.MeanZeroWeightedEnergy

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators ENNReal
open NumberField MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)
def actualEnd : KPMeanZeroWeightedEnergy.End F ζ hζ H.totallyComplex
 (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U) where
 atlas := KPContFlatCuspIncomingEvaluation.atlas F ζ hζ C R P H U
 component := a.1
 cusp := a.2

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (hι : Function.Injective ι) (f : ℂ → S)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
theorem parameterScalar_zero_coordinates (s:ℂ) (p:KPCuspCharts.Coordinates F) :
 KPContActualChamberMeanZeroAdapter.parameterScalar F ζ hζ C R P H U a ι f 0 s
   (KPCuspCharts.toArch F p) =
 KPContActualChamberMeanZeroAdapter.meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s p.2 p.1.1 p.1.2 1 := by
 simp only [KPContActualChamberMeanZeroAdapter.parameterScalar,iteratedDerivWithin_zero,
   KPContActualChamberMeanZeroAdapter.meanZero]
 change KPContActualChamberMeanZeroAdapter.meanZeroJetSheet F ζ hζ C R P H U a ι f 0 s
   (((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension).symm
     ((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension) p)).2)
   (((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension).symm
     ((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension) p)).1.1)
   (((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension).symm
     ((KPCuspCharts.toArchHomeomorph F (KPContFlatCuspIncomingEvaluation.geometry F ζ hζ C R P H U a).positive_dimension) p)).1.2) 1 = _
 rw [Homeomorph.symm_apply_apply]

open KPContFlatCuspIncomingEvaluation
private theorem inv_fix {a c:ℂ} (ha:a≠0) (h:a*c=c) : a⁻¹*c=c := by
 calc a⁻¹*c = a⁻¹*(a*c) := congrArg (a⁻¹ * ·) h.symm
      _ = c := by rw [← mul_assoc,inv_mul_cancel₀ ha,one_mul]
private theorem average_fix {I:Type*} [Fintype I] [Nonempty I] (w:I→ℂ) (c:ℂ)
 (hw:∀i,w i*c=c) : ((Fintype.card I:ℂ)⁻¹*∑i,w i)*c=c := by
 rw [mul_assoc,Finset.sum_mul]
 simp_rw [hw]
 simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
 rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_mul]
theorem projectedScalar_reconstruct (c:ℂ)
 (hdeck : ∀l:(parabolic F ζ hζ C R P H U a).L,
  (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
    ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ)*c=c)
 (hcentral : ∀η:KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U),
  (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ)*c=c) :
 projectedScalar F ζ hζ C R P H U a (fun ε => (KPCuspGenuineMonodromy.chi F ζ hζ ε:ℂ)*c)=c := by
 letI := Fintype.ofFinite (rootsOfUnity 3 F)
 letI := (monodromy F ζ hζ C R P H U a).finite_deck
 letI := Fintype.ofFinite (TranslationDeck F ζ hζ C R P H U a)
 letI := Fintype.ofFinite (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U))
 have hs : ((Fintype.card (rootsOfUnity 3 F):ℂ)⁻¹ * ∑ε:rootsOfUnity 3 F,
   (KPCuspGenuineMonodromy.chi F ζ hζ ε:ℂ)⁻¹*((KPCuspGenuineMonodromy.chi F ζ hζ ε:ℂ)*c)) = c := by
   simp only [←mul_assoc,inv_mul_cancel₀ (Units.ne_zero _),one_mul]
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
   rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_mul]
 unfold projectedScalar
 rw [hs,mul_assoc]
 rw [average_fix _ c (fun η => inv_fix (Units.ne_zero _) (hcentral η))]
 apply average_fix
 intro q
 unfold deckCoefficient
 apply inv_fix (Units.ne_zero _)
 exact hdeck (Quotient.out q)

variable (s:ℂ) (hs:s∈KPContActualChamberNormalSeries.V)
variable (t:ℝ) (b:KPCuspCharts.Shape F)
include hι hf hs in
theorem actualCuspSheet_sheet_identity (x:KPCuspCharts.Horizontal F) (ε:rootsOfUnity 3 F) :
 KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b ε =
 (KPCuspGenuineMonodromy.chi F ζ hζ ε:ℂ)*
 KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b 1 := by
 have hce : cuspGroup F ζ hζ C R P H U a t x b ε =
   KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * cuspGroup F ζ hζ C R P H U a t x b 1 := by
   unfold cuspGroup localGroup finiteRepresentative
   simp only [map_one,one_mul]
   have hcomm (g:KPGlobalTorusFunctionData.G F ζ hζ) : g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε =
      KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g :=
     Subgroup.mem_center_iff.mp (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) g
   change _ * (_ * (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * _ * _)) = _
   simp only [←mul_assoc]
   rw [hcomm]
   simp only [mul_assoc]
   rfl
 simp only [KPContActualChamberCasimirJets.cuspSheet,KPContActualChamberCasimirJets.jet,iteratedDerivWithin_zero,hce]
 exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.1 ε _
include hι hf hs in
theorem actualCuspSheet_rawMean_deck_fixed (l:(parabolic F ζ hζ C R P H U a).L) :
 (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
    ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ)*
 (∫z:KernelTorus F ζ hζ C R P H U a,
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
   ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
 (∫z:KernelTorus F ζ hζ C R P H U a,
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
   ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) := by
 letI := KPContActualChamberOutgoingAdapter.kernelTorus_borelSpace F ζ hζ C R P H U a
 letI := KPContinuation.ChamberOutgoingSource.actual_fiberMeasure_isAddHaarMeasure F ζ hζ C R P H U a
 let φ : KernelTorus F ζ hζ C R P H U a → ℂ := fun z =>
   KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
 have hm (z:KernelTorus F ζ hζ C R P H U a) : φ (z + QuotientAddGroup.mk (KPCuspCharts.embedding F l.val)) =
   (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
    ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ)*φ z := by
   dsimp only [φ]
   change KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t
     (Quotient.out (z + QuotientAddGroup.mk (KPCuspCharts.embedding F l.val))) b 1 =
     (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a
       ((parabolic F ζ hζ C R P H U a).inclusion (Multiplicative.ofAdd l))) : ℂ)*
       KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
   rw [← KPContinuation.ChamberModerateGrowth.actualCuspSheet_translation F ζ hζ C R P H U ι hι f hf a s hs l]
   apply KPContinuation.ChamberModerateGrowth.actualCuspSheet_kernel_representative F ζ hζ C R P H U ι hι f hf a s hs
   calc
     _ = z + QuotientAddGroup.mk (KPCuspCharts.embedding F l.val) := Quotient.out_eq _
     _ = QuotientAddGroup.mk (Quotient.out z + KPCuspCharts.embedding F l.val) := by
       rw [QuotientAddGroup.mk_add]
       congr 1
       exact (Quotient.out_eq z).symm
 rw [← integral_const_mul]
 change (∫z, _ * φ z ∂_) = ∫z,φ z ∂_
 simp_rw [←hm]
 exact integral_add_right_eq_self _ _
include hι hf hs in
theorem actualCuspSheet_central_fixed (η:KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U))
 (x:KPCuspCharts.Horizontal F) :
 (KPCuspGenuineMonodromy.chi F ζ hζ η.val:ℂ)*
 KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b 1 =
 KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t x b 1 := by
 let c := KPCuspGenuineMonodromy.central F ζ hζ η.val
 have hc : c ∈ (atlasLevel F ζ hζ C R P H U).toOpenSubgroup := η.property
 have hu : c.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
   rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U]
   exact ⟨c,hc,rfl⟩
 let g := cuspGroup F ζ hζ C R P H U a t x b 1
 have hcomm : g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ η.val =
    KPSmoothLocalQuotientCharts.centreMap F ζ hζ η.val * g :=
   Subgroup.mem_center_iff.mp (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨η.val,rfl⟩) g
 change _ * KPContActualChamberNormalSeries.E F ζ hζ U ι f s g =
   KPContActualChamberNormalSeries.E F ζ hζ U ι f s g
 calc
   _ = KPContActualChamberNormalSeries.E F ζ hζ U ι f s
     (KPSmoothLocalQuotientCharts.centreMap F ζ hζ η.val * g) :=
     ((KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.1 η.val g).symm
   _ = KPContActualChamberNormalSeries.E F ζ hζ U ι f s
     (g * KPSmoothLocalQuotientCharts.centreMap F ζ hζ η.val) := congrArg _ hcomm.symm
   _ = _ := (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.2.1 g ⟨c.val,hu⟩

include hι hf hs in

theorem actualCuspSheet_rawMean_central_fixed
    (η : KPContSectorPhaseComponentCharts.centralLevel F ζ hζ (atlasLevel F ζ hζ C R P H U)) :
    (KPCuspGenuineMonodromy.chi F ζ hζ η.val : ℂ) *
      (∫ z : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
      ∫ z : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  exact actualCuspSheet_central_fixed F ζ hζ C R P H U a ι hι f hf s hs t b η (Quotient.out z)

include hι hf hs in

theorem actualCuspSheet_projection_eq_rawMean :
    (KPContActualChamberCasimirJets.cuspProjection F ζ hζ C R P H U ι f a
      (KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) 0 s t b).val 0 =
    ∫ z : KernelTorus F ζ hζ C R P H U a,
      KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
      ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
  unfold KPContActualChamberCasimirJets.cuspProjection
  rw [zeroProjection_formula]
  have he (ε : rootsOfUnity 3 F) :
      (∫ z : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b ε
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
      (∫ z : KernelTorus F ζ hζ C R P H U a,
        KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
        ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a) := by
    calc
      _ = ∫ z : KernelTorus F ζ hζ C R P H U a,
          (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
            KPContActualChamberCasimirJets.cuspSheet F ζ hζ C R P H U ι f a 0 s t (Quotient.out z) b 1
            ∂KPContActualChamberOutgoingAdapter.fiberMeasure F ζ hζ C R P H U a := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact actualCuspSheet_sheet_identity F ζ hζ C R P H U a ι hι f hf s hs t b (Quotient.out z) ε
      _ = _ := integral_const_mul _ _
  rw [funext he]
  exact projectedScalar_reconstruct F ζ hζ C R P H U a _
    (actualCuspSheet_rawMean_deck_fixed F ζ hζ C R P H U a ι hι f hf s hs t b)
    (actualCuspSheet_rawMean_central_fixed F ζ hζ C R P H U a ι hι f hf s hs t b)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualMeanZeroSection

end
