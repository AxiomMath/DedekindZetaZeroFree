module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.ScalarRealizationClosure

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalarSmooth_exists_right_level
    (P₀ : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (v : KPGlobalTorusFunctionData.BorelFunctions F ζ hζ P₀)
    (hv : v ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ P₀) :
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        v.val (g * u.val) = v.val g := by
  obtain ⟨b, rfl⟩ := LinearMap.mem_range.mp hv
  let fixed := fun b : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P₀ =>
    ∃ U : KPMsRationalCompactCrossPairing.Level F ζ hζ,
      ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
        b.val (g * u.val) = b.val g
  have hb : fixed b.val := by
    apply Submodule.iSup_induction _ (motive := fixed) b.property
    · intro U b hb
      exact ⟨U, hb.2⟩
    · obtain ⟨U, hU⟩ := (rawSmoothCarrier_closed F ζ hζ).1.2.2
      exact ⟨U, fun _ _ => rfl⟩
    · intro b c hb hc
      obtain ⟨U, hU⟩ := hb
      obtain ⟨V, hV⟩ := hc
      let W : KPMsRationalCompactCrossPairing.Level F ζ hζ :=
        ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup,
          U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
      have hWU : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono inf_le_left
      have hWV : KPGlobalTorusFunctionData.globalLevel F ζ hζ W ≤
          KPGlobalTorusFunctionData.globalLevel F ζ hζ V := Subgroup.map_mono inf_le_right
      refine ⟨W, ?_⟩
      intro g u
      change b.val _ + c.val _ = b.val g + c.val g
      rw [hU g ⟨u.val, hWU u.property⟩, hV g ⟨u.val, hWV u.property⟩]
  obtain ⟨U, hU⟩ := hb
  refine ⟨U, ?_⟩
  intro g u
  simp only [KPGlobalTorusBorelTwistCompatibility.scalarSection_formula, hU g u]

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end
