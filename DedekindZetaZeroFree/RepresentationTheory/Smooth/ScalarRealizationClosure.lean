module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.AdditivePeriodization
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology InnerProductSpace ComplexOrder
namespace DedekindZetaZeroFree.KPGlobalResidualKernel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rawSmoothCarrier : Set (KPMsFixedHaarDisintegration.X F ζ hζ → ℂ) :=
  {f | KPSmoothActualFlowData.SmoothAutomorphic F ζ hζ f ∧
    (∀ ε x, f (KPSmoothActualFlowData.rightTranslate F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) x) =
        (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f x) ∧
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      ∀ (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) x,
        f (KPSmoothActualFlowData.rightTranslate F ζ hζ u.val x) = f x}

theorem rawSmoothCarrier_closed :
    (0 : KPMsFixedHaarDisintegration.X F ζ hζ → ℂ) ∈ rawSmoothCarrier F ζ hζ ∧
    (∀ f g, f ∈ rawSmoothCarrier F ζ hζ → g ∈ rawSmoothCarrier F ζ hζ →
      f + g ∈ rawSmoothCarrier F ζ hζ) ∧
    (∀ (z : ℂ) f, f ∈ rawSmoothCarrier F ζ hζ → z • f ∈ rawSmoothCarrier F ζ hζ) := by
  have hfinite : ActualFiniteFactor.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    congr 1
    ext x
    simp [PGLComplex.AdelicSlicesRaw.finiteSubgroup,
      PGLComplex.AdelicSlicesRaw.finiteTuples,
      KPGlobalTorusFunctionData.finitePart, Subgroup.mem_iInf]
  have hlevel : Nonempty (KPMsRationalCompactCrossPairing.Level F ζ hζ) := by
    obtain ⟨J, _⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ
      Set.univ (Filter.univ_mem)
    have h : Nonempty (CompactOpenLevel (ActualFiniteFactor.finiteSubgroup F ζ hζ)) :=
      ⟨⟨(ActualFiniteFactor.productLevel F ζ hζ J).subgroup,
        (ActualFiniteFactor.productLevel F ζ hζ J).compact⟩⟩
    rw [hfinite] at h
    exact h
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨continuous_const, fun _ => contDiff_const⟩, ?_, ?_⟩
    · intro ε x
      simp
    · obtain ⟨U⟩ := hlevel
      exact ⟨U, fun _ _ => rfl⟩
  · intro f g hf hg
    rcases hf with ⟨hf, hfg, U, hU⟩
    rcases hg with ⟨hg, hgg, V, hV⟩
    refine ⟨⟨hf.1.add hg.1, fun x => (hf.2 x).add (hg.2 x)⟩, ?_, ?_⟩
    · intro ε x
      change f _ + g _ = _ * (f x + g x)
      rw [hfg ε x, hgg ε x, mul_add]
    · let W : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
        ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
          U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
      have hWU : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
        Subgroup.map_mono inf_le_left
      have hWV : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ V :=
        Subgroup.map_mono inf_le_right
      refine ⟨W, ?_⟩
      intro u x
      change f _ + g _ = f x + g x
      rw [hU ⟨u.val, hWU u.property⟩ x, hV ⟨u.val, hWV u.property⟩ x]
  · intro z f hf
    rcases hf with ⟨hf, hfg, U, hU⟩
    refine ⟨⟨continuous_const.smul hf.1,
      fun x => contDiff_const.smul (hf.2 x)⟩, ?_, U, ?_⟩
    · intro ε x
      change z * f _ = _ * (z * f x)
      rw [hfg ε x]
      ring
    · intro u x
      change z * f _ = z * f x
      rw [hU u x]
end DedekindZetaZeroFree.KPGlobalResidualKernel

end
