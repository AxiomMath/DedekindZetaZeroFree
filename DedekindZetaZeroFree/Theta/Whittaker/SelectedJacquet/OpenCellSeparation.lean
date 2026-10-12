module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.OpenCellGeometry
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.SelectedFourierChamber

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts TraceHaarTransport
open KPAdelicCoverRestrictedProduct KPLiteralScalarHCCompactOrbit MeasureTheory
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def openCellFiniteArgument (b : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ :=
  openCellFiniteFactor F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ) *
    openCellFiniteUpper F ζ hζ b

def openCellComplexAmplitude (s : ℂ) (h : KPLiteralTensor.harmonicPlus)
    (g : ComplexGL2) (x : ℂ) : ℂ :=
  literalLocalDeformation s h (weyl * upperUnipotent x * g) *
    star (character (standardComplexParameter : ℂ) x : ℂ)

theorem openCell_fourier_separation (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ (s : ℂ) (a : InfiniteAdeleRing F)
        (t : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
        (g : InfinitePlace F → ComplexGL2),
        f.val s (KPRationalAdelicSplitting.pglW F ζ hζ *
          KPGlobalTorusFunctionData.N F ζ hζ (a,t) * archMatrixInsertion F ζ hζ g) *
          star (adelicTraceCharacter F ((a,t) : KPAdeles F) : ℂ) =
        ∑ i, (b i * literalArchProduct F ζ hζ K f (openCellFiniteArgument F ζ hζ t) (p i) *
          literalFiniteDeformation F ζ hζ K hK s (openCellFiniteArgument F ζ hζ t) *
          star (adelicTraceCharacter F ((0,t) : KPAdeles F) : ℂ)) *
          ∏ w, openCellComplexAmplitude s (h i w) (g w) (archTraceCoordinates F ζ hζ a w) := by
  obtain ⟨n,p,b,h,he⟩ := literalFlat_full_separation F ζ hζ K hK f
  refine ⟨n,p,b,h,?_⟩
  intro s a t g
  rw [openCell_arch_finite, adelicTraceCharacter_arch_finite F ζ hζ a t,
    show ((openCellFiniteFactor F ζ hζ (KPRationalAdelicSplitting.WTuple F ζ hζ)) *
      openCellFiniteUpper F ζ hζ t) = openCellFiniteArgument F ζ hζ t from rfl,
    he, star_mul, star_prod, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [openCellComplexAmplitude, Finset.prod_mul_distrib]
  ring

end DedekindZetaZeroFree.SheetRescaling

end
