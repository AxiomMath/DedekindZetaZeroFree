module

public import DedekindZetaZeroFree.Metaplectic.Weil.ArchimedeanCentralAction

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentRawArchCenter
open KPAdelicCoverRestrictedProduct MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S:SArithmeticData F} {η:RayClassCharacter F S.modulus}
variable (R:PrincipalMellin.ActualRecipe S η)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem fourier_center (dq:Measure (KPAdditiveQuotient F)) (f:Functions R)
    (hf:f∈regularResidualFunctions R) (ε:rootsOfUnity 3 F) (g:Group R) :
    fourier R dq f (pglCentralInjection F ζ hζ ε*g)=
      (KPGlobalTorusFunctionData.iota F ζ hζ ε:ℂ)*fourier R dq f g := by
  have hc : ∀a:Group R,a*pglCentralInjection F ζ hζ ε=pglCentralInjection F ζ hζ ε*a :=
    Subgroup.mem_center_iff.mp (pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩)
  unfold MomentSources.fourier
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [←mul_assoc,hc,mul_assoc,hf.2.2 ε]
  ring

theorem raw_arch_fourier (h:RestrictedCover F ζ hζ)
    (hh:∀q:KPFinitePlace F,h (Sum.inr q)=1) :
    ∃ε:rootsOfUnity 3 F,∀(dq:Measure (KPAdditiveQuotient F))(f:Functions R),
    f∈regularResidualFunctions R → ∀a:Group R,
    fourier R dq f (scalarQuotient F ζ hζ (amalgamation F ζ hζ h)*a)=
      (KPGlobalTorusFunctionData.iota F ζ hζ ε:ℂ)*
      fourier R dq f (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ h)))*a) := by
  obtain ⟨ε,he⟩ := raw_arch_center F ζ hζ h hh
  refine ⟨ε,?_⟩
  intro dq f hf a
  conv_lhs => rw [he]
  have hc : ∀b:Group R,b*pglCentralInjection F ζ hζ ε=pglCentralInjection F ζ hζ ε*b :=
    Subgroup.mem_center_iff.mp (pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩)
  rw [hc,mul_assoc]
  exact fourier_center R dq f hf ε _
end DedekindZetaZeroFree.FourierContinuation.CurrentRawArchCenter

end
