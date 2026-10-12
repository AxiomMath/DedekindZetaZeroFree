module

public import DedekindZetaZeroFree.Theta.Periods.DetectedTensorAssembly
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.ZeroReferenceLimit

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}

def zeroFlat (Q : AdmissibleFlatSources R) :
    KPLiteralRaw.Flat F R.A.zeta12 R.A.primitive_zeta12 Q.K := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · intro s
    refine ⟨⟨continuous_const, fun _ => contDiffOn_const, Q.level, ?_⟩, ?_⟩
    · intros; rfl
    · intros; simp
  · intros; simp
  · refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro k v hv
    have hv0 : v = 0 := by simpa using hv
    subst v
    exact Submodule.zero_mem _

def zeroSources (Q : AdmissibleFlatSources R) : AdmissibleFlatSources R where
  K := Q.K
  iwasawa := Q.iwasawa
  flat := fun _ => zeroFlat Q
  finite_companions := Q.finite_companions
  level := Q.level
  common_level := by intros; rfl
  ordinary := by intros; simp [zeroFlat]
  exterior_spherical := by intros; rfl
  dq := Q.dq
  quotientHaar := Q.quotientHaar
  probability := Q.probability

def zeroRealization (Q : AdmissibleFlatSources R) (T : Realization R Q) :
    Realization R (zeroSources Q) where
  E := fun _ _ => 0
  meromorphic := by intros; exact analyticOnNhd_const.meromorphicOn
  chamber := by intros; simp [KPLiteralRaw.eisenstein, zeroSources, zeroFlat]
  radius := T.radius
  radius_pos := T.radius_pos
  disc_domain := T.disc_domain
  cleared := fun _ _ => 0
  clears := by intros; simp
  smooth := by
    intros
    exact ⟨continuous_const, fun _ => contDiffOn_const, Q.level, by intros; rfl⟩
  common_cleared_level := by intros; rfl
  analytic := by intros; exact analyticOnNhd_const
  coefficients := fun _ _ => 0
  coefficients_smooth := by
    intros
    exact ⟨continuous_const, fun _ => contDiffOn_const, Q.level, by intros; rfl⟩
  compact_smooth_taylor := by
    intro v g m C hC hsub r hr hrR ε hε
    refine ⟨0, ?_⟩
    intro M hM s hs x hx
    simpa using hε
  automorphic := by
    intro v
    refine ⟨⟨continuous_const, fun _ => contDiffOn_const, Q.level, by intros; rfl⟩, ?_, ?_⟩
    · intros; rfl
    · intros; simp

def zeroTensorActions (D : TensorHC R N) : TensorActions R N := by
  letI : Infinite (KPFinitePlace F) := finitePlaces_infinite F
  letI : Infinite (KPHilbert.Place F) := Infinite.of_injective
    (Sum.inr : KPFinitePlace F → KPHilbert.Place F) Sum.inr_injective
  letI : Subsingleton (RestrictedTensorSimple.Core (actualLocal R D.finiteData)
    (fun _ => 0) D.bad) := zeroReferenceCore_subsingleton _ _
  refine {
    aligned := D.aligned
    transport := D.transport
    transport_exact := D.transport_exact
    sources := zeroSources D.sources
    realization := zeroRealization D.sources D.realization
    finiteData := D.finiteData
    references := fun _ => 0
    bad := D.bad
    bad_exact := D.bad_exact
    scalarSlot := D.scalarSlot
    coreMap := 0
    selected := fun _ => 0
    selected_eq := ?_
    selected_frozen_stage := ?_
    core_injective := ?_
    regular := ?_
    generated := ?_
    finite_intertwining := ?_
    complex_intertwining := ?_ }
  · intro v; rfl
  · intro v
    refine ⟨⟨D.bad, le_rfl⟩, fun _ => 0, rfl, ?_⟩
    exact Subsingleton.elim _ _
  · intro x y _; exact Subsingleton.elim _ _
  · intro x; exact Submodule.zero_mem _
  · intro x; exact Submodule.zero_mem _
  · intros; rfl
  · intros; rfl

theorem tensorActions_nonempty (prior : Nonempty (TensorHC R N)) :
    Nonempty (TensorActions R N) := by
  obtain ⟨D⟩ := prior
  exact ⟨zeroTensorActions D⟩

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
