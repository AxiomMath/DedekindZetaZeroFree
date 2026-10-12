module

public import DedekindZetaZeroFree.Theta.Whittaker.CompletedPeriodCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources FourierContinuation FourierContinuation.ComplexLines
open KPCplxActualImage KPCplxWhittakerUnique
open KPActualReflectionData.StandardLocalSource
open KPReferenceChange.StandardComplexImage
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

 theorem factorization_complex_ell (D : TensorLocalLines R N) (w : InfinitePlace F) :
    D.factorization.ell (Sum.inl w)=D.localEll (Sum.inl w) := by
  letI : DecidableEq (KPHilbert.Place F) := FourierContinuation.instDecidableEqPlace
  dsimp only [TensorLocalLines.factorization]
  exact Function.update_of_ne (by simp) _ _

theorem traceWhittaker_actual (w : InfinitePlace F)
    (L : Theta traceFrequency →L[ℂ] ℂ)
    (hL : L ∈ whittakerSpace traceFrequency traceCharacter) :
    L ∈ localWhittakerSpace _ (Theta frequency) (complexRootAction R.A w)
      (complexRawPsi w).toAddChar.toMonoidHom := by
  intro t v
  change L (complexRootAction R.A w (Multiplicative.ofAdd t.toAdd) v)=
    (complexRawPsi w).toAddChar t.toAdd*L v
  rw [complexRootAction_apply,complexRawPsi_trace,trace_character]
  exact hL (coordinate R.A w t.toAdd) v

theorem factorization_smooth_forms (D : TensorLocalLines R N)
    (hline : ∀w, D.toTensorHC.sliceLine (Sum.inl w)≤traceLine) :
    ∃ L : ∀w:InfinitePlace F, Theta frequency →L[ℂ] ℂ,
      (∀w v,L w (coreInStandardImage v)=D.factorization.ell (Sum.inl w) v) ∧
      (∀w,L w∈localWhittakerSpace _ (Theta frequency) (complexRootAction R.A w)
        (complexRawPsi w).toAddChar.toMonoidHom) ∧
      (∀w,L w sphericalSeed ≠ 0) := by
  have hex (w : InfinitePlace F) : ∃L:Theta traceFrequency →L[ℂ] ℂ,
      L∈whittakerSpace traceFrequency traceCharacter ∧
      restriction L=D.localEll (Sum.inl w) := by
    exact Submodule.mem_map.mp (hline w (D.localEll_mem (Sum.inl w)))
  choose L hL he using hex
  have hr (w : InfinitePlace F) (v : KPGlobalResidualConstruction.complexCore) :
      L w (coreInStandardImage v)=D.factorization.ell (Sum.inl w) v := by
    rw [factorization_complex_ell]
    exact LinearMap.congr_fun (he w) v
  have hw (w : InfinitePlace F) := traceWhittaker_actual (R:=R) w (L w) (hL w)
  refine ⟨L,hr,hw,?_⟩
  intro w
  have hn : L w ≠ 0 := by
    intro hz
    apply D.localEll_ne (Sum.inl w)
    rw [←he w,hz,map_zero]
  have h := continuous_whittaker_sphericalCore_ne_zero R.A w (L w) (hw w) hn
  simpa only [coreInStandardImage_spherical] using h
theorem factorization_trace_forms (D : TensorLocalLines R N)
    (hline : ∀w, D.toTensorHC.sliceLine (Sum.inl w)≤traceLine) :
    ∃ L : ∀w:InfinitePlace F, Theta frequency →L[ℂ] ℂ,
      (∀w v,L w (coreInStandardImage v)=D.factorization.ell (Sum.inl w) v) ∧
      (∀w,L w∈whittakerSpace traceFrequency traceCharacter) ∧
      (∀w,L w sphericalSeed ≠ 0) := by
  have hex (w : InfinitePlace F) : ∃L:Theta traceFrequency →L[ℂ] ℂ,
      L∈whittakerSpace traceFrequency traceCharacter ∧
      restriction L=D.localEll (Sum.inl w) := by
    exact Submodule.mem_map.mp (hline w (D.localEll_mem (Sum.inl w)))
  choose L hL he using hex
  have hr (w : InfinitePlace F) (v : KPGlobalResidualConstruction.complexCore) :
      L w (coreInStandardImage v)=D.factorization.ell (Sum.inl w) v := by
    rw [factorization_complex_ell]
    exact LinearMap.congr_fun (he w) v
  have hw (w : InfinitePlace F) := traceWhittaker_actual (R:=R) w (L w) (hL w)
  refine ⟨L,hr,hL,?_⟩
  intro w
  have hn : L w ≠ 0 := by
    intro hz
    apply D.localEll_ne (Sum.inl w)
    rw [←he w,hz,map_zero]
  have h := continuous_whittaker_sphericalCore_ne_zero R.A w (L w) (hw w) hn
  simpa only [coreInStandardImage_spherical] using h
end DedekindZetaZeroFree.RootDerivatives

end
