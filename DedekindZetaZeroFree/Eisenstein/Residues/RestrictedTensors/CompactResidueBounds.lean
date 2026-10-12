module

public import DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.WordL2

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12

include N in
theorem restrictedSlot_residue_compact_bound
    (D : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (HR : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (HP : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (M : NativeMeasuredSource F ζ hζ HR HP)

    (dk : Measure (KPMsGreenFlux.K F)) [IsProbabilityMeasure dk] [dk.IsHaarMeasure]
    (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
    (x : ∀j : s.val, LiteralSource.Plus R.A P C j.val)
    (w : InfinitePlace F) (hw : Sum.inl w∈s.val)
    (K : Set (KPLiteralRaw.G F ζ hζ)) (hK : IsCompact K) :
    ∃orders : Finset ℕ, ∃B : ℝ, 0<B ∧ ∀v : complexCore, ∀g∈K,
      ‖LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g‖ ≤
        B*(orders.sup coreSeminorm) v := by
  obtain ⟨J,os₀,B₀,hB₀,hJ,hx⟩ := restrictedSlot_quotient_residue_l2 R N P C D HR HP M  dk s x w hw
  let U := EisensteinSmoothGerms.ScalarSource.atlasLevel F ζ hζ J
  obtain ⟨W,hW,Cs,hCs,hsob⟩ := ResidualOutputSobolev.exists_original_compact_bound_raw
    U HR HP (nativeFamily F ζ hζ HR HP) K hK
  choose os B hB hb using fun b => restrictedSlot_residue_word_l2 R N P C D HR HP M  dk s x w hw b
  let orders := W.biUnion os
  let Bt : ℝ := (∑b∈W,B b)+1
  have hBt : 0 < Bt := by
    have hn : 0 ≤ ∑b∈W,B b := Finset.sum_nonneg (fun b _ => (hB b).le)
    dsimp [Bt]
    linarith
  refine ⟨orders,Cs*Bt,mul_pos hCs hBt,?_⟩
  intro v g hg
  let f := LiteralSource.coreResidueQuotient R P C (restrictedSlotTensor R.A P C s x w hw v)
  have hpin : (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) =
      LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) := funext (hx v).2.1
  have hsmooth : KPLiteralRaw.Smooth F ζ hζ
      (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)) := by
    rw [hpin]
    exact (LiteralSource.coreResidue_raw_automorphic R P C _).1
  have hlevel (u : U.toOpenSubgroup) (a : KPLiteralRaw.G F ζ hζ) :
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (a*u.val.val)) =
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a) := by
    rw [show f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ (a*u.val.val)) = _ from (hx v).2.1 _,
      show f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ a) = _ from (hx v).2.1 _]
    apply hJ v a u.val.val
    rw [EisensteinSmoothGerms.ScalarSource.level_matching]
    exact ⟨u.val,u.property,rfl⟩
  have hmem (b) (h : b∈W) : MemLp (ResidualOutputSobolev.quotientWord b f) 2 HR.quotientHaar :=
    ((hx v).1 (b.map (KPMsClearedTruncationL2.NativeWordBridge.wordIndexEquiv F))).2
  have hnorm (b) (h : b∈W) : lpNorm (ResidualOutputSobolev.quotientWord b f) 2 HR.quotientHaar ≤
      Bt*(orders.sup coreSeminorm) v := by
    have hsub : os b ⊆ orders := Finset.subset_biUnion_of_mem os h
    have hm : (os b).sup coreSeminorm v ≤ orders.sup coreSeminorm v :=
      (Finset.sup_mono (f:=coreSeminorm) hsub) v
    have hsum : B b ≤ Bt := by
      have hh := Finset.single_le_sum (fun b _ => (hB b).le) h
      dsimp [Bt]
      linarith
    exact (hb b v).trans ((mul_le_mul_of_nonneg_left hm (hB b).le).trans
      (mul_le_mul_of_nonneg_right hsum (apply_nonneg _ _)))
  have hfinal := hsob f hsmooth hlevel hmem (Bt*(orders.sup coreSeminorm) v)
    (mul_nonneg hBt.le (apply_nonneg _ _)) hnorm g hg
  rw [show f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)=_ from (hx v).2.1 g] at hfinal
  exact hfinal.trans_eq (mul_assoc Cs Bt _).symm

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
