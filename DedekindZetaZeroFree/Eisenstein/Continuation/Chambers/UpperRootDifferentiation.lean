module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSections.UpperRootDifferentiation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

 theorem chamber_value_majorant {K : Subgroup (MomentSources.Group R)}
    (hK : IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K)
    (f : Flat F R.A.zeta12 R.A.primitive_zeta12 K) (s : ℂ) (hs : (1/3 : ℝ) < s.re)
    (T : Set (MomentSources.Group R)) (hT : IsCompact T) :
    ∃ B : KPChamberBruhatTwoCells.RationalQuotient F → ℝ, Summable B ∧
      ∀ c g, g ∈ T → ‖f.val s (rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * g)‖ ≤ B c := by
  obtain ⟨B,hB,hbound⟩ := KPLiteralChamber.chamber_jet_majorants F R.A.zeta12 R.A.primitive_zeta12
    K hK f {s} isCompact_singleton (by intro z hz; subst z; exact hs) T hT ⟨0,fun i => Fin.elim0 i⟩
  refine ⟨B,hB,?_⟩
  intro c g hg
  have h := hbound c s rfl g hg
  rw [KPLiteralChamber.rightJet_compactExtension_rational_eq] at h
  simpa only [KPLiteralChamber.rightJet, iteratedFDeriv_zero_apply,
    KPInterface.ResidueConstruction.Raw.archChart_base, mul_one] using h

theorem upper_chamber_affine {K : Subgroup (MomentSources.Group R)}
    (hK : IwasawaCompact F R.A.zeta12 R.A.primitive_zeta12 K)
    (f v u : Flat F R.A.zeta12 R.A.primitive_zeta12 K)
    (w : InfinitePlace F) (b : Bool)
    (hsource : ∀ s g, MomentSources.upperLieDerivative R w b (f.val s) g = v.val s g + s * u.val s g)
    (s : ℂ) (hs : (1/3 : ℝ) < s.re) (g : MomentSources.Group R) :
    HasDerivAt (fun t => eisenstein F R.A.zeta12 R.A.primitive_zeta12 K f s (g * upperCurve R w b t))
      (eisenstein F R.A.zeta12 R.A.primitive_zeta12 K v s g +
        s * eisenstein F R.A.zeta12 R.A.primitive_zeta12 K u s g) 0 := by
  letI : IsTopologicalGroup (MomentSources.Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  have hc : Continuous (upperCurve R w b) := by
    rw [show upperCurve R w b = fun t => archChart F R.A.zeta12 R.A.primitive_zeta12 (upperCoordinates w b t) from
      funext (fun t => (upperCoordinates_chart R w b t).symm)]
    apply continuousOn_univ.mp
    exact (ActualMovingCompact.archChart_continuousOn F R.A.zeta12 R.A.primitive_zeta12).comp
      (upperCoordinates_smooth w b).continuous.continuousOn
      (fun t _ v => by simp [upperCoordinates])
  let T := (fun t => g * upperCurve R w b t) '' Metric.closedBall (0 : ℝ) 1
  have hT : IsCompact T := (isCompact_closedBall (0 : ℝ) 1).image (continuous_const.mul hc)
  obtain ⟨V,hV,hVbound⟩ := chamber_value_majorant R hK v s hs T hT
  obtain ⟨U,hU,hUbound⟩ := chamber_value_majorant R hK u s hs T hT
  let term := fun (c : KPChamberBruhatTwoCells.RationalQuotient F) t => f.val s
    (rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * (g * upperCurve R w b t))
  let dterm := fun (c : KPChamberBruhatTwoCells.RationalQuotient F) t => v.val s
    (rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * (g * upperCurve R w b t)) +
    s * u.val s (rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * (g * upperCurve R w b t))
  have hd (c) (t : ℝ) (_ : t ∈ Metric.ball (0 : ℝ) 1) : HasDerivAt (term c) (dterm c t) t := by
    have hh := upperCurve_hasDerivAt R w b (f.val s) (f.property.1 s).1
      (rationalLift F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out c) * g) t
    simp only [mul_assoc, hsource] at hh
    exact hh
  have hbound (c) (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) 1) : ‖dterm c t‖ ≤ V c + ‖s‖ * U c := by
    have htT : g * upperCurve R w b t ∈ T := ⟨t,Metric.ball_subset_closedBall ht,rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hVbound c _ htT)
      (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hUbound c _ htT) (norm_nonneg _)))
  have hsum : Summable (fun c => ‖term c 0‖) := by
    simpa only [term, upperCurve_zero, mul_one] using
      (KPLiteralExceptionalResidue.chamberConvergence F R.A.zeta12 R.A.primitive_zeta12 K hK f s hs g).norm
  have hh := hasDerivAt_tsum_of_isPreconnected (hV.add (hU.mul_left ‖s‖)) Metric.isOpen_ball
    (convex_ball (0 : ℝ) 1).isPreconnected hd hbound (Metric.mem_ball_self (by norm_num))
    hsum.of_norm (Metric.mem_ball_self (by norm_num))
  dsimp [term,dterm] at hh
  simp only [upperCurve_zero, mul_one] at hh
  rw [Summable.tsum_add (KPLiteralExceptionalResidue.chamberConvergence F R.A.zeta12 R.A.primitive_zeta12 K hK v s hs g)
    ((KPLiteralExceptionalResidue.chamberConvergence F R.A.zeta12 R.A.primitive_zeta12 K hK u s hs g).mul_left s), tsum_mul_left] at hh
  exact hh

end DedekindZetaZeroFree.RootDerivatives

end
