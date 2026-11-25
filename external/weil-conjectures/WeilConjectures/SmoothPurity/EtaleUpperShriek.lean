/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SmoothPurity.Defs
public import WeilConjectures.TraceFormula.PurityDevissage

/-!
# The exceptional inverse image along an étale morphism

Let `h : U ⟶ V` be an étale morphism of separated `k`-schemes of finite type. On bounded
constructible `ℚ̄_ℓ`-complexes, the exceptional inverse image `Rh^!` is the pullback `h^*`
(`ProEtale.CondensedRing.boundedConstructibleUpperStarIsoUpperShriekOfEtale`), so that the lower
shriek `Rh_!` is left adjoint to `h^*`
(`ProEtale.CondensedRing.boundedConstructibleEtaleLowerShriekUpperStarAdjunction`). This is
purity in relative dimension zero (SGA 4, Exposé XVIII, 3.2.5):

* the purity map `γ_{h,K} : h^* K ⊗ Rh^! ℚ̄_ℓ ⟶ Rh^! K` is an isomorphism for every `K`, `h` being
  smooth (`ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`);
* `Rh^! ℚ̄_ℓ ≅ ℚ̄_ℓ(0)[0] ≅ ℚ̄_ℓ`, by smooth purity in relative dimension `0`
  (`ProEtale.CondensedRing.isIso_smoothPurityMap`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {U V : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
  (h : U ⟶ V) [Etale h.left]

/-- **Purity at the unit for an étale morphism**, `Rh^! ℚ̄_ℓ,V ≅ ℚ̄_ℓ,U`: the inverse of the
purity map `ℚ̄_ℓ,U(0)[0] ⟶ Rh^! ℚ̄_ℓ,V` of `h`, smooth of relative dimension `0`, followed by
`ℚ̄_ℓ,U(0)[0] ≅ ℚ̄_ℓ,U`. -/
def boundedConstructibleUpperShriekUnitIsoOfEtale :
    (boundedConstructibleUpperShriek ℓ h).obj
        (𝟙_ (Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) ≅
      𝟙_ (Dᵇc(U.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  (asIso (smoothPurityMap ℓ h 0)).symm ≪≫
    (ObjectProperty.fullyFaithfulι _).preimageIso
      ((shiftFunctorZero' _ (2 * ((0 : ℕ) : ℤ)) (by simp)).app _ ≪≫
        tateTwistDerivedZeroIso ℓ U.left)

instance (K : Dᵇc(V.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekUnitTensorMapNatTrans ℓ h).app K) :=
  isIso_upperShriekUnitTensorMap_of_smooth ℓ h K

instance : IsIso (upperShriekUnitTensorMapNatTrans ℓ h) :=
  NatIso.isIso_of_isIso_app _

/-- **The exceptional inverse image along an étale morphism is the pullback**, `h^* ≅ Rh^!`, on
bounded constructible `ℚ̄_ℓ`-complexes: `h^* K ≅ h^* K ⊗ ℚ̄_ℓ ≅ h^* K ⊗ Rh^! ℚ̄_ℓ ≅ Rh^! K`, by
purity at the unit (`boundedConstructibleUpperShriekUnitIsoOfEtale`) and the purity map
(`upperShriekUnitTensorMap`). -/
def boundedConstructibleUpperStarIsoUpperShriekOfEtale :
    boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h ≅
      boundedConstructibleUpperShriek ℓ h :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (rightUnitorNatIso _).symm ≪≫
    Functor.isoWhiskerLeft _
      ((curriedTensor _).flip.mapIso (boundedConstructibleUpperShriekUnitIsoOfEtale ℓ h).symm) ≪≫
    asIso (upperShriekUnitTensorMapNatTrans ℓ h) ≪≫ Functor.leftUnitor _

/-- **`Rh_! ⊣ h^*` for an étale morphism `h`** on bounded constructible `ℚ̄_ℓ`-complexes: the
adjunction `Rh_! ⊣ Rh^!` transported along `Rh^! ≅ h^*`
(`boundedConstructibleUpperStarIsoUpperShriekOfEtale`). -/
def boundedConstructibleEtaleLowerShriekUpperStarAdjunction :
    boundedConstructibleLowerShriek ℓ h ⊣
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h :=
  (boundedConstructibleUpperShriekAdjunction ℓ h).ofNatIsoRight
    (boundedConstructibleUpperStarIsoUpperShriekOfEtale ℓ h).symm

end AlgebraicGeometry.ProEtale.CondensedRing
