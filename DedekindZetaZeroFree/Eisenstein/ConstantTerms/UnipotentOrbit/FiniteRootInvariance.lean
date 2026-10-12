module

public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.UnipotentOrbit.AdelicDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open KPContFlatCuspIncomingEvaluation
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
variable (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable (f : ℂ → S) (hι : Function.Injective ι)
variable (hf : DifferentiableOn ℂ f KPContinuation.spectralDomain)
variable (s : ℂ) (hs : s ∈ KPContActualChamberNormalSeries.V)
variable (a : Cusps F ζ hζ C R P H U) (t : ℝ) (b : KPCuspCharts.Shape F) (ε : rootsOfUnity 3 F)
include hι hf hs in

theorem actual_upper_orbit_finite_root_invariant (z : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
 (hz : (finiteRepresentative F ζ hζ C R P H U a 1)⁻¹ * finiteRoot F ζ hζ z *
   finiteRepresentative F ζ hζ C R P H U a 1 ∈ (atlasLevel F ζ hζ C R P H U).toOpenSubgroup)
 (x : KPGlobalTorusFunctionData.Adeles F) :
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s
   (KPGlobalTorusFunctionData.N F ζ hζ (x + finiteParameter F z) * localGroup F ζ hζ C R P H U a t 0 b ε) =
 KPContActualChamberNormalSeries.E F ζ hζ U ι f s
   (KPGlobalTorusFunctionData.N F ζ hζ x * localGroup F ζ hζ C R P H U a t 0 b ε) := by
 let c := finiteRepresentative F ζ hζ C R P H U a 1
 let u := c⁻¹ * finiteRoot F ζ hζ z * c
 have hcε : finiteRepresentative F ζ hζ C R P H U a ε = KPCuspGenuineMonodromy.central F ζ hζ ε * c := by
   simp [c,finiteRepresentative,mul_assoc]
 have hcomm : Commute (KPCuspGenuineMonodromy.central F ζ hζ ε) (finiteRoot F ζ hζ z) := by
   apply Commute.symm
   change finiteRoot F ζ hζ z * KPCuspGenuineMonodromy.central F ζ hζ ε =
     KPCuspGenuineMonodromy.central F ζ hζ ε * finiteRoot F ζ hζ z
   apply Subtype.ext
   exact Subgroup.mem_center_iff.mp
     (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε,rfl⟩) _
 have hcu : finiteRoot F ζ hζ z * finiteRepresentative F ζ hζ C R P H U a ε =
   finiteRepresentative F ζ hζ C R P H U a ε * u := by
   rw [hcε]
   dsimp [u]
   rw [← mul_assoc,hcomm.symm.eq]
   group
 have hu : u.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
   rw [EisensteinSmoothGerms.ScalarSource.level_matching F ζ hζ U]
   exact ⟨u,hz,rfl⟩
 have hg : KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z) * localGroup F ζ hζ C R P H U a t 0 b ε =
    localGroup F ζ hζ C R P H U a t 0 b ε * u.val := by
   unfold localGroup
   change (finiteRoot F ζ hζ z).val * (_ * _) = _
   rw [← mul_assoc, (insertion_commutes_cover F ζ hζ _ (finiteRoot F ζ hζ z)).symm.eq,mul_assoc]
   rw [show (finiteRoot F ζ hζ z).val * (finiteRepresentative F ζ hζ C R P H U a ε).val =
      (finiteRepresentative F ζ hζ C R P H U a ε).val * u.val from congrArg Subtype.val hcu]
   simp [mul_assoc]
 rw [KPGlobalTorusFunctionData.N_add,mul_assoc,hg,← mul_assoc]
 exact (KPContActualChamberNormalSeries.covariance F ζ hζ U ι f hι hf s hs).2.2.1 _ ⟨u.val,hu⟩
end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
