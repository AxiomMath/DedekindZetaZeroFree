module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.CompactFaithfulness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open NumberField MeasureTheory KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts
open KPReferenceChange.StandardComplexImage.FamilyCorrect TraceHaarTransport
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem openCell_finite_base (a : InfiniteAdeleRing F)
    (b : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (g : InfinitePlace F → ComplexGL2) :
    KPRationalAdelicSplitting.pglW F ζ hζ *
      KPGlobalTorusFunctionData.N F ζ hζ (a,b) *
        (c.val * archMatrixInsertion F ζ hζ g) =
    (openCellFiniteArgument F ζ hζ b * c).val * archMatrixInsertion F ζ hζ
      (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w) * g w) := by
  have hc := (archMatrixInsertion_commutes_finite F ζ hζ g c).eq
  rw [← hc, ← mul_assoc, openCell_arch_finite]
  have hc' := (archMatrixInsertion_commutes_finite F ζ hζ
    (fun w => weyl * upperUnipotent (archTraceCoordinates F ζ hζ a w) * g w) c).eq
  simp only [Subgroup.coe_mul, openCellFiniteArgument]
  rw [mul_assoc, hc', ← mul_assoc]

theorem finiteBase_fourier_separation (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ (s : ℂ) (a : InfiniteAdeleRing F)
        (t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
        (g : InfinitePlace F → ComplexGL2),
        f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
          KPGlobalTorusFunctionData.N F ζ hζ (a,t) * (c.val * archMatrixInsertion F ζ hζ g)) *
          star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ) =
        ∑ i, (b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t * c) (p i) *
          literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t * c) *
          star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)) *
          ∏ w, openCellComplexAmplitude s (h i w) (g w) (archTraceCoordinates F ζ hζ a w) := by
  obtain ⟨n,p,b,h,he⟩ := literalFlat_full_separation F ζ hζ K hK f
  refine ⟨n,p,b,h,?_⟩
  intro s a t c g
  rw [openCell_finite_base, adelicTraceCharacter_arch_finite F ζ hζ a t,
    he, star_mul, star_prod, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [openCellComplexAmplitude, Finset.prod_mul_distrib]
  ring

theorem finiteBase_arch_integral_separation (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ s : ℂ, s ∈ chamber → ∀ (t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (g : InfinitePlace F → ComplexGL2),
        Integrable (fun a : InfiniteAdeleRing F =>
          f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
            KPGlobalTorusFunctionData.N F ζ hζ (a,t) * (c.val * archMatrixInsertion F ζ hζ g)) *
            star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ)) (KPAdditiveHaar.archMeasure F) ∧
        (∫ a : InfiniteAdeleRing F,
          f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
            KPGlobalTorusFunctionData.N F ζ hζ (a,t) * (c.val * archMatrixInsertion F ζ hζ g)) *
            star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ) ∂KPAdditiveHaar.archMeasure F) =
        ∑ i, (b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t * c) (p i) *
          literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t * c) *
          star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)) *
            ∏ w, spectralJacquet (h i w).val s (g w) := by
  obtain ⟨n,p,b,h,he⟩ := finiteBase_fourier_separation F ζ hζ K hK f
  refine ⟨n,p,b,h,?_⟩
  intro s hs t c g
  let d := fun i => b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t * c) (p i) *
    literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t * c) *
    star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)
  let k := fun i (a : InfiniteAdeleRing F) => ∏ w,
    openCellComplexAmplitude s (h i w) (g w) (archTraceCoordinates F ζ hζ a w)
  have hk (i) := openCellComplexProduct_integral F ζ hζ s hs (h i) g
  have hi : ∀ i, Integrable (fun a => d i * k i a) (KPAdditiveHaar.archMeasure F) :=
    fun i => (hk i).1.const_mul _
  have hident : (fun a : InfiniteAdeleRing F => f.val s
      (KPRationalAdelicSplitting.pglW F ζ hζ * KPGlobalTorusFunctionData.N F ζ hζ (a,t) *
        (c.val * archMatrixInsertion F ζ hζ g)) *
      star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ)) =
      (fun a => ∑ i, d i * k i a) := funext (fun a => he s a t c g)
  rw [hident]
  refine ⟨integrable_finset_sum _ (fun i _ => hi i), ?_⟩
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  exact congrArg (d i * ·) (hk i).2

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
