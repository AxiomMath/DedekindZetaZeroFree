module

public import DedekindZetaZeroFree.Eisenstein.Induction.Cusps.IncomingSheetEvaluation
public import DedekindZetaZeroFree.Eisenstein.Induction.Spherical.CompactJetHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContFlatCuspCoefficientTransition

open KPContFlatCuspIncomingEvaluation

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : Cusps F ζ hζ C R P H U)

def zeroFiberEvaluation : ZeroFiber F ζ hζ C R P H U a →ₗ[ℂ] ℂ where
  toFun f := f.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zeroFiberEvaluation_injective :
    Function.Injective (zeroFiberEvaluation F ζ hζ C R P H U a) := by
  intro f g h
  apply Subtype.ext
  funext z
  exact (f.property.2 z).trans (h.trans (g.property.2 z).symm)

instance zeroFiberNormedAddCommGroup : NormedAddCommGroup (ZeroFiber F ζ hζ C R P H U a) :=
  NormedAddCommGroup.induced _ ℂ (zeroFiberEvaluation F ζ hζ C R P H U a)
    (zeroFiberEvaluation_injective F ζ hζ C R P H U a)

instance zeroFiberNormedSpace : NormedSpace ℂ (ZeroFiber F ζ hζ C R P H U a) :=
  NormedSpace.induced ℂ _ ℂ (zeroFiberEvaluation F ζ hζ C R P H U a)

instance zeroFiberFiniteDimensional : FiniteDimensional ℂ (ZeroFiber F ζ hζ C R P H U a) :=
  (frequencies F ζ hζ C R P H U a).constantSystem.finiteDimensional

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]

 def stageCoordinates : S ≃ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
  (Module.finBasis ℂ S).equivFun

 abbrev stageNormedAddCommGroup : NormedAddCommGroup S :=
  NormedAddCommGroup.induced _ _ (stageCoordinates (S := S)).toLinearMap
    (stageCoordinates (S := S)).injective

attribute [local instance] stageNormedAddCommGroup

 abbrev stageNormedSpace : NormedSpace ℂ S :=
  NormedSpace.induced ℂ _ _ (stageCoordinates (S := S)).toLinearMap

attribute [local instance] stageNormedSpace

variable (ι : S →ₗ[ℂ] KPContFlatCommonLevelKernel.CommonSphericalStage F ζ hζ U)

def frameCoefficient (shape : KPCuspCharts.Shape F) (s : ℂ) :
    S →L[ℂ] ZeroFiber F ζ hζ C R P H U a :=
  ((zeroProjection F ζ hζ C R P H U a).comp
    (sheetEvaluation F ζ hζ C R P H U a ι s)).toContinuousLinearMap

theorem frameCoefficient_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (shape : KPCuspCharts.Shape F) :
    frameCoefficient F ζ hζ C R P H U a ι shape s v =
      (b F ζ hζ C R P H U a ι s hs v).val shape := by
  rfl

theorem locally_parallel (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (j : Fin (geometry F ζ hζ C R P H U a).atlas.chartCount) :
    IsLocallyConstant (fun shape : (geometry F ζ hζ C R P H U a).atlas.shapeLift j =>
      (b F ζ hζ C R P H U a ι s hs v).val shape.val) := by
  have h : (fun shape : (geometry F ζ hζ C R P H U a).atlas.shapeLift j =>
      (b F ζ hζ C R P H U a ι s hs v).val shape.val) =
      Function.const _ ((b F ζ hζ C R P H U a ι s hs v).val
        (Classical.arbitrary (KPCuspCharts.Shape F))) := by
    funext shape; rfl
  rw [h]
  exact IsLocallyConstant.const _

theorem transport_formula (s : ℂ) (hs : s ∈ KPContinuation.spectralDomain)
    (v : S) (g : stabilizer F ζ hζ C R P H U a) (shape : KPCuspCharts.Shape F) :
    let shape' := shape + KPCuspLogShape.logarithm F H.totallyComplex
      (parabolic F ζ hζ C R P H U a).E
      (parabolic F ζ hζ C R P H U a).integralUnits
      (Additive.ofMul ((parabolic F ζ hζ C R P H U a).ratio g))
    (b F ζ hζ C R P H U a ι s hs v).val shape' =
      (frequencies F ζ hζ C R P H U a).constantSystem.transport
        ((parabolic F ζ hζ C R P H U a).ratio g)
        ((b F ζ hζ C R P H U a ι s hs v).val shape) ∧
    ∀ z : KernelTorus F ζ hζ C R P H U a,
      ((b F ζ hζ C R P H U a ι s hs v).val shape').val z =
        (KPCuspGenuineMonodromy.chi F ζ hζ (rho F ζ hζ C R P H U a g) : ℂ) *
          ((b F ζ hζ C R P H U a ι s hs v).val shape).val
            ((monodromy F ζ hζ C R P H U a).monodromy g⁻¹ z) := by
  have h1 := (b F ζ hζ C R P H U a ι s hs v).property g shape
  refine ⟨h1, ?_⟩
  intro z
  rw [h1]
  exact (frequencies F ζ hζ C R P H U a).constantSystem.transition_formula g
    ((b F ζ hζ C R P H U a ι s hs v).val shape) z

 instance instFintypeCentralLevel
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    Fintype (KPContSectorPhaseComponentCharts.centralLevel F ζ hζ U) :=
  Fintype.ofFinite _

 instance instFintypeRootsOfUnity : Fintype (rootsOfUnity 3 F) :=
  Fintype.ofFinite _

 def sheetComponent (ε : rootsOfUnity 3 F) :
    S →L[ℂ] (rootsOfUnity 3 F → ℂ) :=
  (((LinearMap.proj ε).comp (sheetEvaluation F ζ hζ C R P H U a ι 0)).smulRight
    (Pi.single ε (1 : ℂ))).toContinuousLinearMap

private lemma sheetEvaluation_toContinuousLinearMap_eq_sum (s : ℂ) :
    (sheetEvaluation F ζ hζ C R P H U a ι s).toContinuousLinearMap =
      ∑ ε : rootsOfUnity 3 F,
        Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ)) •
          sheetComponent F ζ hζ C R P H U a ι ε := by
  ext v ε'
  change sheetEvaluation F ζ hζ C R P H U a ι s v ε' =
    (∑ ε : rootsOfUnity 3 F,
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
        (finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ)) •
        sheetComponent F ζ hζ C R P H U a ι ε) v ε'
  rw [sheetEvaluation_formula F ζ hζ C R P H U a ι s v ε']
  simp only [sum_apply, Finset.sum_apply, smul_apply, Pi.smul_apply, sheetComponent,
    LinearMap.coe_toContinuousLinearMap', LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single ε']
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne' hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ ε') h

private lemma differentiableOn_postcompose
    {E₀ E₁ E₂ : Type*} [AddCommGroup E₀] [Module ℂ E₀] [TopologicalSpace E₀]
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂]
    (T : E₁ →L[ℂ] E₂) {f : E₀ → E₁} {Ω : Set E₀}
    (hf : DifferentiableOn ℂ f Ω) : DifferentiableOn ℂ (fun x => T (f x)) Ω := by
  intro x hx
  obtain ⟨f', hf'⟩ := hf x hx
  refine ⟨T.comp f', ⟨?_⟩⟩
  have h := (T.isBigOTVS_fun_comp
    (f := fun p : E₀ × E₀ => f p.1 - f p.2 - f' (p.1 - p.2))).trans_isLittleOTVS
    (HasFDerivAtFilter.isLittleOTVS hf')
  simpa only [map_sub, ContinuousLinearMap.comp_apply] using h

theorem frameCoefficient_holomorphic
    (j : Fin (geometry F ζ hζ C R P H U a).atlas.chartCount)
    (shape : (geometry F ζ hζ C R P H U a).atlas.shapeLift j) :
    DifferentiableOn ℂ (frameCoefficient F ζ hζ C R P H U a ι shape.val)
      KPContinuation.spectralDomain := by
  let Z := (zeroProjection F ζ hζ C R P H U a).toContinuousLinearMap
  let W : rootsOfUnity 3 F → (S →L[ℂ] ZeroFiber F ζ hζ C R P H U a) :=
    fun ε => Z.comp (sheetComponent F ζ hζ C R P H U a ι ε)
  let T : (rootsOfUnity 3 F → ℂ) →ₗ[ℂ]
      (S →L[ℂ] ZeroFiber F ζ hζ C R P H U a) :=
    { toFun := fun c => ∑ ε, c ε • W ε
      map_add' := by
        intro c d
        ext v z
        simp only [sum_apply, smul_apply, Pi.smul_apply, add_apply,
          Pi.add_apply, Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul,
          Finset.sum_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c d
        ext v z
        simp only [sum_apply, smul_apply, Pi.smul_apply, Submodule.coe_sum,
          Submodule.coe_smul, Finset.sum_apply, smul_eq_mul,
          Finset.mul_sum, mul_assoc, RingHom.id_apply] }
  have hpi : DifferentiableOn ℂ
      (fun s : ℂ => fun ε : rootsOfUnity 3 F =>
        Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
          (finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ)))
      KPContinuation.spectralDomain := by
    apply differentiableOn_pi.mpr
    intro ε
    exact (differentiableOn_id.mul_const _).cexp
  have h := differentiableOn_postcompose T.toContinuousLinearMap hpi
  apply h.congr
  intro s hs
  change frameCoefficient F ζ hζ C R P H U a ι shape.val s =
    ∑ ε : rootsOfUnity 3 F,
      Complex.exp (s * (KPContFlatSourceRecipe.alpha F ζ hζ
        (finiteRepresentative F ζ hζ C R P H U a ε).val : ℂ)) •
        Z.comp (sheetComponent F ζ hζ C R P H U a ι ε)
  have heq : frameCoefficient F ζ hζ C R P H U a ι shape.val s =
      Z.comp (sheetEvaluation F ζ hζ C R P H U a ι s).toContinuousLinearMap := by
    ext v
    rfl
  rw [heq, sheetEvaluation_toContinuousLinearMap_eq_sum F ζ hζ C R P H U a ι s,
    ContinuousLinearMap.comp_finsetSum]
  simp only [ContinuousLinearMap.comp_smul]

end DedekindZetaZeroFree.KPContFlatCuspCoefficientTransition

namespace DedekindZetaZeroFree

end DedekindZetaZeroFree

end
