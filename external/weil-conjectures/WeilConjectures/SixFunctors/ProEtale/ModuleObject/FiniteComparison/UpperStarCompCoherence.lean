/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EquivalenceCompCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# The finite-coefficient comparison and the composition of pullbacks

Let `T` be a finite discrete commutative ring and `Φ = ProEtale.finiteCoefficientModEquivalence`.
The isomorphisms `ProEtale.lowerStarFiniteCoefficientModEquivalenceIso` are compatible with the
composition isomorphisms of the pushforwards
(`ProEtale.lowerStarFiniteCoefficientModEquivalenceIso_comp`): on underlying abelian sheaves all
of them are identities or the composition isomorphism `ProEtale.lowerStarComp Ab`. By conjugation,
the isomorphisms `ProEtale.upperStarFiniteCoefficientModEquivalenceIso` are compatible with the
composition isomorphisms of the pullbacks
(`ProEtale.upperStarFiniteCoefficientModEquivalenceIso_compCoherence`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The isomorphisms `lowerStarFiniteCoefficientModEquivalenceIso` are compatible with the
composition isomorphisms of the pushforwards. -/
lemma lowerStarFiniteCoefficientModEquivalenceIso_comp
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (finiteCoefficientModEquivalence Z T).functor.map
        ((CondensedRing.lowerStarComp (Profinite.continuousMapRingObj T) f g).hom.app N) ≫
        (lowerStarFiniteCoefficientModEquivalenceIso (f ≫ g) T).hom.app N =
      (lowerStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((CondensedRing.lowerStar (Profinite.continuousMapRingObj T) f).obj N) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).map
          ((lowerStarFiniteCoefficientModEquivalenceIso f T).hom.app N) ≫
        (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) f g).hom.app
          ((finiteCoefficientModEquivalence X T).functor.obj N) := by
  apply (sheafCompose (Scheme.ProEt.topology Z)
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} T)) Ab.{u + 1})).map_injective
  rfl

/-- **The finite-coefficient comparison is compatible with the composition of pullbacks**: the
isomorphisms `upperStarFiniteCoefficientModEquivalenceIso` are compatible with the composition
isomorphisms of the pullbacks of module objects and of sheaves of `T`-modules. -/
theorem upperStarFiniteCoefficientModEquivalenceIso_compCoherence :
    CompCoherence (CondensedRing.upperStarComp (Profinite.continuousMapRingObj T) f g)
      (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) f g)
      (upperStarFiniteCoefficientModEquivalenceIso g T)
      (upperStarFiniteCoefficientModEquivalenceIso f T)
      (upperStarFiniteCoefficientModEquivalenceIso (f ≫ g) T) :=
  Adjunction.compCoherence_of_equivalence_conjugate _ _ _ _ _ _ _ _ _
    (lowerStarFiniteCoefficientModEquivalenceIso f T)
    (lowerStarFiniteCoefficientModEquivalenceIso g T)
    (lowerStarFiniteCoefficientModEquivalenceIso (f ≫ g) T)
    (CondensedRing.lowerStarComp (Profinite.continuousMapRingObj T) f g)
    (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1} T)) f g)
    (lowerStarFiniteCoefficientModEquivalenceIso_comp T f g) _ _ rfl rfl _ _ _ rfl rfl rfl

end AlgebraicGeometry.ProEtale
