module

public import DedekindZetaZeroFree.Adeles.Lattices.Cusps.ParabolicTranslations
public import DedekindZetaZeroFree.Adeles.Lattices.FiniteAdeles.TripleCompactOpenSubgroup
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.BoundaryFlux.AngularConormalDescent
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspGeometry.ConormalFirstJet

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology MatrixGroups
open NumberField

namespace DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

private theorem finiteBase_finiteRoot_principal (r : F) : KPCuspGenuineMonodromy.finiteBase F ζ hζ
 (finiteRoot F ζ hζ (algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r)) =
 KPFiniteComponents.diagonal F (KPChamberBruhatTwoCells.rationalUnipotent F r) := by
 let x := finiteParameter F (algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r)
 change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
   (KPAdelicCoverRestrictedProduct.projection F ζ hζ (KPRationalAdelicSplitting.N F ζ hζ x))) = _
 rw [KPFiniteComponents.diagonal, KPChamberBruhatTwoCells.rationalUnipotent,
   Matrix.ProjGenLinGroup.map_mk]
 congr 1
 apply Units.ext
 apply Matrix.ext
 intro i j
 apply Subtype.ext
 funext q
 have h := congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M i j)
   (KPRationalAdelicSplitting.projection_N F ζ hζ x (Sum.inr q))
 convert h using 1
 · rfl
 · fin_cases i <;> fin_cases j <;> rfl
private theorem rationalUnipotent_fixes_infinity (r : F) : KPChamberBruhatTwoCells.rationalUnipotent F r • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
 unfold KPChamberBruhatTwoCells.rationalUnipotent KPCuspArithmetic.infinity
 rw [Projectivization.PGL.mk_smul_mk]
 congr 1
 ext i
 fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
variable (a : KPContFlatCuspIncomingEvaluation.Cusps F ζ hζ C R P H U)

open KPContFlatCuspIncomingEvaluation

private theorem rational_parameter_mem_actual_parabolic (r:F)
 (hr : (finiteRepresentative F ζ hζ C R P H U a 1)⁻¹ *
 finiteRoot F ζ hζ (algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r) *
 finiteRepresentative F ζ hζ C R P H U a 1 ∈ (atlasLevel F ζ hζ C R P H U).toOpenSubgroup) :
 r ∈ (parabolic F ζ hζ C R P H U a).L := by
 let σ := sigma F ζ hζ C R P H U a
 let γ := σ * KPChamberBruhatTwoCells.rationalUnipotent F r * σ⁻¹
 let g := (atlas F ζ hζ C R P H U).representative a.1
 let u := (finiteRepresentative F ζ hζ C R P H U a 1)⁻¹ *
   finiteRoot F ζ hζ (algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r) *
   finiteRepresentative F ζ hζ C R P H U a 1
 have hdiag (δ : KPCuspArithmetic.PGL2 F) :
     KPCuspGenuineMonodromy.finiteBase F ζ hζ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ δ) =
       KPFiniteComponents.diagonal F δ :=
   DFunLike.congr_fun (KPCuspGenuineMonodromy.finite_cover_exact F ζ hζ).2.2.2.1 δ
 have hc : finiteRepresentative F ζ hζ C R P H U a 1 =
   (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ σ)⁻¹ * g := by
   simp [finiteRepresentative, σ, g, map_inv]
 have hγ : γ ∈ component F ζ hζ C R P H U a := by
   change KPFiniteComponents.diagonal F γ ∈
     (((atlasLevel F ζ hζ C R P H U).toOpenSubgroup.toSubgroup.map (KPCuspGenuineMonodromy.finiteBase F ζ hζ)).map
       (MulAut.conj (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)).toMonoidHom)
   refine ⟨KPCuspGenuineMonodromy.finiteBase F ζ hζ u, ⟨u, hr, rfl⟩, ?_⟩
   change KPCuspGenuineMonodromy.finiteBase F ζ hζ g * KPCuspGenuineMonodromy.finiteBase F ζ hζ u *
      (KPCuspGenuineMonodromy.finiteBase F ζ hζ g)⁻¹ = _
   dsimp [u, γ]
   rw [hc]
   simp only [map_mul, map_inv, hdiag, finiteBase_finiteRoot_principal]
   group
 have hq : γ ∈ MulAction.stabilizer (KPCuspArithmetic.PGL2 F)
   (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2) := by
   change γ • _ = _
   rw [← ((atlas F ζ hζ C R P H U).cuspAtlas a.1).representative_formula a.2]
   change (σ * KPChamberBruhatTwoCells.rationalUnipotent F r * σ⁻¹) • (σ • KPCuspArithmetic.infinity F) = σ • KPCuspArithmetic.infinity F
   rw [mul_smul, mul_smul, inv_smul_smul, rationalUnipotent_fixes_infinity]
 apply mem_parabolicL_of_rationalUnipotent_mem
 change KPChamberBruhatTwoCells.rationalUnipotent F r ∈
   (component F ζ hζ C R P H U a ⊓ MulAction.stabilizer (KPCuspArithmetic.PGL2 F)
      (((atlas F ζ hζ C R P H U).cuspAtlas a.1).cusp a.2)).map (MulAut.conj σ⁻¹).toMonoidHom
 refine ⟨γ, ⟨hγ,hq⟩, ?_⟩
 simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
 dsimp [γ]
 group

theorem actual_cusp_finite_kernel_level :
    ∃ K : AddSubgroup (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      IsCompact (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (K : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) ∧
      (∀ x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F, x ∈ K →
        (KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1)⁻¹ *
          KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.finiteRoot F ζ hζ x *
          KPContFlatCuspIncomingEvaluation.finiteRepresentative F ζ hζ C R P H U a 1 ∈
            (KPContFlatCuspIncomingEvaluation.atlasLevel F ζ hζ C R P H U).toOpenSubgroup) ∧
      (∀ r : F, algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) r ∈ K →
        r ∈ KPCuspGenuineMonodromy.kernelLattice
          (KPContFlatCuspIncomingEvaluation.stabilizer F ζ hζ C R P H U a)
          (KPContFlatCuspIncomingEvaluation.parabolic F ζ hζ C R P H U a)
          (KPContFlatCuspIncomingEvaluation.rho F ζ hζ C R P H U a)) := by
  obtain ⟨K₀, hc₀, ho₀, hroot₀⟩ := small_conjugated_finite_root_level F ζ hζ
    (atlasLevel F ζ hζ C R P H U) (finiteRepresentative F ζ hζ C R P H U a 1)
  obtain ⟨hc, ho, hle, hdivide⟩ := triple_finite_level F K₀ hc₀ ho₀
  refine ⟨K₀.map (nsmulAddMonoidHom 3), hc, ho, ?_, ?_⟩
  · intro x hx
    exact hroot₀ x (hle hx)
  · intro r hr
    obtain ⟨r₀, hr₀, he⟩ := hdivide r hr
    have hL : r₀ ∈ (parabolic F ζ hζ C R P H U a).L :=
      rational_parameter_mem_actual_parabolic F ζ hζ C R P H U a r₀
        (hroot₀ _ hr₀)
    rw [← he]
    exact triple_mem_kernelLattice _ _ _ ⟨r₀, hL⟩

end DedekindZetaZeroFree.KPContinuation.ChamberOutgoingSource

end
