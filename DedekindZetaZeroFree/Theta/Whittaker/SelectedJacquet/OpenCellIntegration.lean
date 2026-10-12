module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SpectralJacquet
public import DedekindZetaZeroFree.MeasureTheory.Bochner.FiniteDimensionalFunctionSpaces

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField MeasureTheory KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts TraceHaarTransport
local instance : (characterHaar standardComplexParameter).IsAddHaarMeasure :=
  characterHaar_isAddHaarMeasure _
open KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit
open KPReferenceChange.StandardComplexImage.FamilyCorrect
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem openCellComplexAmplitude_integrable (s : ℂ) (hs : s ∈ chamber)
    (h : KPLiteralTensor.harmonicPlus) (g : ComplexGL2) :
    Integrable (openCellComplexAmplitude s h g) (characterHaar standardComplexParameter) := by
  unfold openCellComplexAmplitude
  simpa only [literalLocalDeformation_eq_plusValue] using
    spectralJacquet_integrable h.val s hs g

theorem openCellComplexProduct_integral (s : ℂ) (hs : s ∈ chamber)
    (h : InfinitePlace F → KPLiteralTensor.harmonicPlus)
    (g : InfinitePlace F → ComplexGL2) :
    Integrable (fun a : InfiniteAdeleRing F => ∏ w,
      openCellComplexAmplitude s (h w) (g w) (archTraceCoordinates F ζ hζ a w))
        (KPAdditiveHaar.archMeasure F) ∧
    (∫ a : InfiniteAdeleRing F, ∏ w,
      openCellComplexAmplitude s (h w) (g w) (archTraceCoordinates F ζ hζ a w)
        ∂KPAdditiveHaar.archMeasure F) = ∏ w, spectralJacquet (h w).val s (g w) := by
  let k := fun w x => openCellComplexAmplitude s (h w) (g w) x
  have hk := Integrable.fintype_prod_dep (fun w => openCellComplexAmplitude_integrable s hs (h w) (g w))
  refine ⟨(integrable_archTraceCoordinates_iff F ζ hζ _).mpr hk, ?_⟩
  change (∫ a, (fun x : InfinitePlace F → ℂ => ∏ w, k w (x w))
    (archTraceCoordinates F ζ hζ a) ∂KPAdditiveHaar.archMeasure F) = _
  apply (integral_archTraceCoordinates F ζ hζ (fun x => ∏ w, k w (x w))).trans
  rw [integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro w _
  unfold spectralJacquet
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [k, openCellComplexAmplitude, literalLocalDeformation_eq_plusValue])

theorem openCell_arch_integral_separation (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ (s : ℂ), s ∈ chamber → ∀ (t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (g : InfinitePlace F → ComplexGL2),
        Integrable (fun a : InfiniteAdeleRing F =>
          f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
            KPGlobalTorusFunctionData.N F ζ hζ (a,t) * archMatrixInsertion F ζ hζ g) *
          star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ)) (KPAdditiveHaar.archMeasure F) ∧
        (∫ a : InfiniteAdeleRing F,
          f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
            KPGlobalTorusFunctionData.N F ζ hζ (a,t) * archMatrixInsertion F ζ hζ g) *
          star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ) ∂KPAdditiveHaar.archMeasure F) =
        ∑ i, (b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t) (p i) *
          literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t) *
          star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)) *
            ∏ w, spectralJacquet (h i w).val s (g w) := by
  obtain ⟨n,p,b,h,he⟩ := openCell_fourier_separation F ζ hζ K hK f
  refine ⟨n,p,b,h,?_⟩
  intro s hs t g
  let c := fun i => b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t) (p i) *
    literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t) *
    star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)
  let k := fun i (a : InfiniteAdeleRing F) => ∏ w,
    openCellComplexAmplitude s (h i w) (g w) (archTraceCoordinates F ζ hζ a w)
  have hk (i) := openCellComplexProduct_integral F ζ hζ s hs (h i) g
  have hi : ∀ i, Integrable (fun a => c i * k i a) (KPAdditiveHaar.archMeasure F) :=
    fun i => (hk i).1.const_mul _
  have hident : (fun a : InfiniteAdeleRing F =>
      f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
        KPGlobalTorusFunctionData.N F ζ hζ (a,t) * archMatrixInsertion F ζ hζ g) *
      star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ)) =
      (fun a => ∑ i, c i * k i a) := funext (fun a => he s a t g)
  rw [hident]
  refine ⟨integrable_finset_sum _ (fun i _ => hi i), ?_⟩
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  exact congrArg (c i * ·) (hk i).2

end DedekindZetaZeroFree.SheetRescaling

end
