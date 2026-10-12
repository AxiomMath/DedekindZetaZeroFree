module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.AngularBound

variable {F : Type} [Field F] [NumberField F]
variable {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem scalarSection_continuous_of_levels
    (P : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hlevel : ∀ (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
      (f : KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J),
      Continuous (fun g : KPGlobalTorusFunctionData.G F ζ hζ =>
        (f.val.val g).val.val 1))
    (f : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ P) :
    Continuous (KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ P f).val := by
  have hval : (KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ P f).val =
      fun g : KPGlobalTorusFunctionData.G F ζ hζ => (f.val.val g).val.val 1 := by
    funext g
    exact KPGlobalTorusBorelTwistCompatibility.scalarSection_formula F ζ hζ P f g
  rw [hval]
  have hmem : f.val ∈ ⨆ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J := f.property
  exact Submodule.iSup_induction
    (motive := fun x : KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ P =>
      Continuous (fun g : KPGlobalTorusFunctionData.G F ζ hζ => (x.val g).val.val 1))
    (fun J => KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ P J) hmem
    (fun J x hx => hlevel J ⟨x, hx⟩)
    (by simpa using continuous_const)
    (fun x y hx hy => by
      convert hx.add hy using 1)

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.AngularBound

end
