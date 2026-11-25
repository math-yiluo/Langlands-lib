/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.SixFunctors.ProEtale.GaloisAcyclic.FieldExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStar

/-!
# Algebraic field base change for module objects over a finite coefficient ring

Let `T` be a finite discrete commutative ring and `Λ = C(-, T)` the corresponding condensed
ring. Let `Ω / L` be an algebraic field extension, `h : G ⟶ Spec L` and `g : G_Ω ⟶ G` the base
change. For a module object `M` over `Λ_G` whose image under the equivalence
`ProEtale.finiteCoefficientModEquivalence` with pro-étale sheaves of `T`-modules is of étale
origin, `g^* M` is acyclic for the pushforward `g_*` of module objects
(`AlgebraicGeometry.ProEtale.rightAcyclic_condensedRingLowerStar_upperStar_of_iso`).

This is transported from the statement for pro-étale sheaves of modules
(`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj`) along
the exact equivalence `ProEtale.finiteCoefficientModEquivalence`, which commutes with pullbacks
and pushforwards, using that acyclicity is invariant under such a transport
(`CategoryTheory.Functor.rightAcyclic_of_rightAcyclic_equivalence_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D'] [HasDerivedCategory C]
  [HasDerivedCategory C'] [HasDerivedCategory D'] [EnoughInjectives C] [EnoughInjectives C']

/-- Acyclicity is invariant under transport along equivalences: if `F ⋙ eD ≅ e ⋙ F'` for
equivalences `e : C ≌ C'` and `eD : D ≌ D'`, and `e M` is `F'`-acyclic, then `M` is
`F`-acyclic. -/
lemma rightAcyclic_of_rightAcyclic_equivalence_obj (e : C ≌ C') (eD : D ≌ D') (F : C ⥤ D)
    (F' : C' ⥤ D') [F.Additive] [F'.Additive] [e.functor.Additive] [eD.functor.Additive]
    (α : F ⋙ eD.functor ≅ e.functor ⋙ F') {M : C}
    (h : F'.rightAcyclic (e.functor.obj M)) : F.rightAcyclic M := by
  intro q
  have := preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms e.symm.toAdjunction
  let eR : (F ⋙ eD.functor).rightDerived (q + 1) ≅ (e.functor ⋙ F').rightDerived (q + 1) :=
    { hom := NatTrans.rightDerived α.hom (q + 1)
      inv := NatTrans.rightDerived α.inv (q + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id] }
  have hz : IsZero (eD.functor.obj ((F.rightDerived (q + 1)).obj M)) :=
    (h q).of_iso ((rightDerivedCompObjIsoOfExact F eD.functor M (q + 1)).symm ≪≫ eR.app M ≪≫
      (rightDerivedCompIsoOfExact e.functor F' (q + 1)).app M)
  exact (eD.inverse.map_isZero hz).of_iso (eD.unitIso.app _)

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

open scoped CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {L Ω : Type u} [Field L] [Field Ω] [Algebra L Ω] [Algebra.IsAlgebraic L Ω]
  {G : Scheme.{u}} (h : G ⟶ Spec (.of L))

/-- **Higher direct images along an algebraic field base change vanish on module objects of
étale origin.** Let `Λ = C(-, T)` for a finite discrete commutative ring `T`, `Ω / L` an
algebraic field extension, `h : G ⟶ Spec L` and `g : G_Ω ⟶ G` the base change. If the image of
a module object `M` over `Λ_G` under `finiteCoefficientModEquivalence` is isomorphic to `ν^* F₀`
for an étale sheaf `F₀` of `T`-modules, then `g^* M` is acyclic for `g_*`. -/
theorem rightAcyclic_condensedRingLowerStar_upperStar_of_iso
    (M : Mod (Sheaf (Scheme.ProEt.topology G) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} T) G))
    (F₀ : Sheaf G.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} T)))
    (hM : Nonempty ((finiteCoefficientModEquivalence G T).functor.obj M ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) G).obj F₀)) :
    ((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))_*⟦
        Profinite.continuousMapRingObj.{u} T⟧).rightAcyclic
      (((pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω))))^*⟦
        Profinite.continuousMapRingObj.{u} T⟧).obj M) := by
  obtain ⟨e⟩ := hM
  set g := pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap L Ω)))
  refine Functor.rightAcyclic_of_rightAcyclic_equivalence_obj
    (finiteCoefficientModEquivalence _ T) (finiteCoefficientModEquivalence G T) _ _
    (lowerStarFiniteCoefficientModEquivalenceIso g T) ?_
  exact (ProEtale.lowerStar _ g).rightAcyclic.prop_of_iso
    ((ProEtale.upperStar _ g).mapIso e.symm ≪≫
      ((upperStarFiniteCoefficientModEquivalenceIso g T).app M).symm)
    (rightAcyclic_lowerStar_upperStar_comparisonUpperStar_obj _ h F₀)

end AlgebraicGeometry.ProEtale
