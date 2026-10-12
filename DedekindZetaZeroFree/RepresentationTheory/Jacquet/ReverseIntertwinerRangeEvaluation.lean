module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Cubic.RegularPointValues
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.OppositeCompositionVanishing

@[expose] public section

namespace DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.RankoneSteps.JacquetWeightSteps
open KPLocalPrincipalSeries KPLocalStoneVonNeumann KPLocalJacquetImage
open scoped Valued
open ValuativeRel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}
variable (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T) (ε : Sign)
 def evalOne : sectionSpace A P ε 0 →ₗ[ℂ] InducedModule P where
  toFun f := f.val 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
 theorem evalOne_root (x : Multiplicative K) :
  (evalOne A P ε).comp ((principalSeries A P ε 0).comp (root A) x) = evalOne A P ε := by
  apply LinearMap.ext
  intro f
  change f.val (1 * root A x) = f.val 1
  rw [one_mul, ← mul_one (root A x)]
  change f.val ((A.upperRoot x : G) * 1) = _
  rw [f.property.1]
  cases ε <;> simp [inducingAction, inducingScalar, deltaHalf, normPower,
    borelAction, A.retract_upperRoot, map_one, localAbs]

def principalSeriesJacquetEvaluation :
  (jacquetRepresentation (V := sectionSpace A P ε 0) A (principalSeries A P ε 0)).IntertwiningMap
    ((inducingAction A P ε 0).comp A.torus) where
  toLinearMap := Representation.Coinvariants.lift _ (evalOne A P ε) (evalOne_root A P ε)
  isIntertwining' h := by
    apply Representation.Coinvariants.hom_ext
    apply LinearMap.ext
    intro f
    change f.val (1 * (A.torus h : G)) = inducingAction A P ε 0 (A.torus h) (f.val 1)
    simpa using f.property.1 (A.torus h) 1

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem jacquetEvaluation_comp_ne_zero (ρ : Representation ℂ G V)
  (f : ρ.IntertwiningMap (principalSeries A P ε 0)) (hf : f ≠ 0) :
  (principalSeriesJacquetEvaluation A P ε).comp (jacquetMap (V := V) (W := sectionSpace A P ε 0) A f) ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext g
  have h := congrArg (fun l : (jacquetRepresentation (V := V) A ρ).IntertwiningMap ((inducingAction A P ε 0).comp A.torus) => l (Representation.Coinvariants.mk (ρ.comp (root A)) (ρ g v))) hz
  change (f (ρ g v)).val 1 = 0 at h
  rw [f.isIntertwining] at h
  simpa [principalSeries, vectorRightTranslation] using h

def jacquetRangeEvaluation (ρ : Representation ℂ G V)
  (f : ρ.IntertwiningMap (principalSeries A P ε 0)) :
  (jacquetMap (V := V) (W := sectionSpace A P ε 0) A f).range.toRepresentation.IntertwiningMap
  ((inducingAction A P ε 0).comp A.torus) where
  toLinearMap := {
    toFun := fun v => principalSeriesJacquetEvaluation A P ε v.val
    map_add' := fun _ _ => (principalSeriesJacquetEvaluation A P ε).map_add _ _
    map_smul' := fun _ _ => (principalSeriesJacquetEvaluation A P ε).map_smul _ _ }
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ((principalSeriesJacquetEvaluation A P ε).isIntertwining' h) v.val

theorem jacquetRangeEvaluation_surjective (ρ : Representation ℂ G V)
  (f : ρ.IntertwiningMap (principalSeries A P ε 0)) (hf : f ≠ 0)
  [Representation.IsIrreducible ((inducingAction A P ε 0).comp A.torus)] :
  Function.Surjective (jacquetRangeEvaluation A P ε ρ f) := by
  apply (Representation.IsIrreducible.surjective_or_eq_zero (jacquetRangeEvaluation A P ε ρ f)).resolve_right
  intro hz
  apply jacquetEvaluation_comp_ne_zero A P ε ρ f hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact congrArg (fun l => l ⟨jacquetMap (V := V) (W := sectionSpace A P ε 0) A f v, v, rfl⟩) hz

end
end DedekindZetaZeroFree.KPExceptionalRaw.FiniteSource.RankoneSteps.JacquetWeightSteps
