module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralChamberAnalytic
open KPLiteralRaw KPLiteralChamber

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem flat_entire (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (g : G F ζ hζ) :
    Differentiable ℂ (fun s => f.val s g) := by
  have he : (fun s => f.val s g) =
      (fun s => compactExtension F ζ hζ K hK (f.val 0) s g) := by
    funext s
    exact (compactExtension_eq_flat F ζ hζ K hK f s g).symm
  rw [he]
  unfold compactExtension KPGlobalExceptionalParameter.realLogPower
  fun_prop

theorem chamber_locally_uniform (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (g : G F ζ hζ) :
    SummableLocallyUniformlyOn
      (fun c : KPChamberBruhatTwoCells.RationalQuotient F =>
        fun s => f.val s (rationalLift F ζ hζ (Quotient.out c) * g))
      {s : ℂ | (1 : ℝ) / 3 < s.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const Complex.continuous_re)
  intro P hPc hP
  obtain ⟨b, hb, hbound⟩ := chamber_scalar_compact_majorants F ζ hζ K hK f
    P hP hPc {g} isCompact_singleton
  exact ⟨b, hb, fun c s hs => hbound c s hs g (Set.mem_singleton g)⟩

theorem raw_chamber_analytic (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (s : ℂ)
    (hs : (1 : ℝ) / 3 < s.re) (g : G F ζ hζ) :
    AnalyticAt ℂ (fun z => eisenstein F ζ hζ K f z g) s := by
  have ho : IsOpen {s : ℂ | (1 : ℝ) / 3 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd := (chamber_locally_uniform F ζ hζ K hK f g).differentiableOn ho
    (fun c z _ => (flat_entire F ζ hζ K hK f
      (rationalLift F ζ hζ (Quotient.out c) * g)) z)
  exact hd.analyticAt (ho.mem_nhds hs)

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.LiteralChamberAnalytic

end
