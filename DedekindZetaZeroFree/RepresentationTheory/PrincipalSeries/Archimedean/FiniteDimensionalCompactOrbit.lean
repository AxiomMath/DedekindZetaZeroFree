module

public import DedekindZetaZeroFree.Algebra.Multilinear.FiniteFunctionProducts

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
open KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open _root_.DedekindZetaZeroFree.ThetaExpansion renaming archSectionHom → archSectionHom
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

theorem archCompact_has_su2 (w : InfinitePlace F)
    (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))
    (hk : k ∈ ThetaExpansion.complexSU2Compact R w) :
    ∃ u : KPCplxCharacterHaar.ComplexSU2,
      k.epsilon = 1 ∧ complexMatrix R w k = KPCplxCharacterHaar.complexSU2Embedding u := by
  have hs : {x | ∃ u : KPCplxCharacterHaar.ComplexSU2, x = archSectionHom R w u} =
      ((archSectionHom R w).range : Set _) := by
    ext x
    exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
  change k ∈ Subgroup.closure {x | ∃ u, x = archSectionHom R w u} at hk
  rw [hs, Subgroup.closure_eq] at hk
  obtain ⟨u, rfl⟩ := hk
  refine ⟨u, rfl, ?_⟩
  apply Units.ext
  ext i j
  simp [complexMatrix, archSectionHom, Matrix.GeneralLinearGroup.map_apply]

def archFunction (w : InfinitePlace F) : PrincipalSeries positiveParameter →ₗ[ℂ] (Raw R → ℂ) where
  toFun f g := (KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12
    R.A.primitive_zeta12 (g (Sum.inl w)).epsilon : ℂ) * f (complexMatrix R w (g (Sum.inl w)))
  map_add' := by intros; ext g; exact mul_add _ _ _
  map_smul' := by intros; ext g; exact mul_left_comm _ _ _

theorem archValue_finite_space (w : InfinitePlace F) (f : Plus R N P C (Sum.inl w)) :
    ∃ U : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ U ∧
      ∀ k : ThetaExpansion.fullProductCompactPreimage R,
        (fun g : Raw R => localValue R N P C (Sum.inl w) ((g * k.val) (Sum.inl w)) f) ∈ U := by
  obtain ⟨V, hV, hf, hstable, _⟩ := KPLiteralScalarArchHarmonicCore.finite_invariant_subspace
    positiveParameter f.val f.property
  letI := hV
  refine ⟨V.map (archFunction R w), inferInstance, ?_⟩
  intro k
  obtain ⟨u, he, hm⟩ := archCompact_has_su2 R w (k.val (Sum.inl w)) (k.property (Sum.inl w))
  let a : compactSubgroup := ⟨Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding u), ⟨u, rfl⟩⟩
  refine Submodule.mem_map.mpr ⟨KPCplxPrincipalSeriesCharts.pi positiveParameter a f.val, hstable a f.val hf, ?_⟩
  funext g
  change _ = localValue R N P C (Sum.inl w) (g (Sum.inl w) * k.val (Sum.inl w)) f
  have hmatrix : complexMatrix R w (g (Sum.inl w) * k.val (Sum.inl w)) =
      complexMatrix R w (g (Sum.inl w)) * KPCplxCharacterHaar.complexSU2Embedding u := by
    have hmul : complexMatrix R w (g (Sum.inl w) * k.val (Sum.inl w)) =
        complexMatrix R w (g (Sum.inl w)) * complexMatrix R w (k.val (Sum.inl w)) := by
      unfold complexMatrix
      change Matrix.GeneralLinearGroup.map _ (_ * _) = _
      exact map_mul _ _ _
    exact hmul.trans (congrArg (fun v => complexMatrix R w (g (Sum.inl w)) * v) hm)
  have heps : (g (Sum.inl w) * k.val (Sum.inl w)).epsilon = (g (Sum.inl w)).epsilon := by
    rw [KPLocalCover.mul_epsilon, KPLocalChartTopology.complex_sigmaTwo_eq_one, he]
    simp
  simp only [archFunction, LinearMap.coe_mk, AddHom.coe_mk, a, pi_mk, localValue]
  rw [hmatrix, heps]
  rfl

theorem pureArchProduct_finite_space (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) :
    ∃ U : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ U ∧
      ∀ k : ThetaExpansion.fullProductCompactPreimage R,
        (fun g : Raw R => pureArchProduct R N P C s f (g * k.val)) ∈ U := by
  choose U hU hmem using fun w => archValue_finite_space R N P C w
    (f ⟨Sum.inl w, s.property (arch_bad R P C w)⟩)
  obtain ⟨V, hV, hv⟩ := finite_product_space Finset.univ U (fun w _ => hU w)
  refine ⟨V, hV, ?_⟩
  intro k
  convert hv (fun w g => localValue R N P C (Sum.inl w) ((g * k.val) (Sum.inl w))
    (f ⟨Sum.inl w, s.property (arch_bad R P C w)⟩)) (fun w _ => hmem w k) using 1
  ext g
  simp [pureArchProduct]

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
