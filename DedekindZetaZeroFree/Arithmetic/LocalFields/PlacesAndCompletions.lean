module

public import DedekindZetaZeroFree.Adeles.Characters.AdditiveQuotient
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open NumberField IsDedekindDomain
open scoped Matrix.Norms.L2Operator

universe u

abbrev KPFinitePlace (F : Type u) [Field F] [NumberField F] :=
  HeightOneSpectrum (RingOfIntegers F)

abbrev KPPlace (F : Type u) [Field F] [NumberField F] :=
  KPFinitePlace F ⊕ InfinitePlace F

def KPCompletion (F : Type u) [Field F] [NumberField F] : KPPlace F → Type u
  | .inl v => v.adicCompletion F
  | .inr v => v.Completion

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    Field (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    TopologicalSpace (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

instance (F : Type u) [Field F] [NumberField F] (v : KPPlace F) :
    Algebra F (KPCompletion F v) := by
  cases v <;> dsimp [KPCompletion] <;> infer_instance

end DedekindZetaZeroFree

end
