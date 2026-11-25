/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# Torsion homology of abelian étale sheaves

The abelian coefficient conditions in the proper base change theorem.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- An abelian sheaf `F` on the small étale site of `X` is *torsion* if the stalk of `F` at
every geometric point of `X` is a torsion abelian group, i.e. every element of every geometric
stalk is killed by a positive integer [Stacks 03SA]. -/
class Scheme.IsTorsionSheaf {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : Prop where
  isTorsion_sheafFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsAddTorsion (↥((pointSmallEtale s).sheafFiber.obj F))

/-- An abelian étale sheaf is torsion in the stalkwise sense
`AlgebraicGeometry.Scheme.IsTorsionSheaf` if and only if it is torsion in the local sense
`CategoryTheory.Sheaf.IsTorsion`: every section is locally torsion. -/
lemma Scheme.isTorsionSheaf_iff_isTorsion {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) : IsTorsionSheaf F ↔ F.IsTorsion :=
  ⟨fun h ↦ (isTorsion_iff_isAddTorsion_sheafFiber F).2 h.isTorsion_sheafFiber,
    fun h ↦ ⟨(isTorsion_iff_isAddTorsion_sheafFiber F).1 h⟩⟩

/-- An abelian étale sheaf isomorphic to a torsion sheaf is torsion. -/
lemma Scheme.IsTorsionSheaf.of_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology Ab.{u + 1}} (e : F ≅ G) [IsTorsionSheaf F] :
    IsTorsionSheaf G where
  isTorsion_sheafFiber Ω _ _ s :=
    IsAddTorsion.of_surjective (f := ((pointSmallEtale s).sheafFiber.map e.hom).hom)
      (ConcreteCategory.bijective_of_isIso _).2 (IsTorsionSheaf.isTorsion_sheafFiber Ω s)

variable (X : Scheme.{u})

/-- An object of the bounded below derived category of abelian étale sheaves has
*torsion cohomology* if all its cohomology sheaves are torsion
(`AlgebraicGeometry.Scheme.IsTorsionSheaf`). This is the hypothesis on the coefficient
complex in the general proper base change theorem. -/
noncomputable def Etale.DerivedCategory.Plus.torsionHomology :
    ObjectProperty (DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) :=
  fun K ↦ ∀ n : ℤ, IsTorsionSheaf
    ((DerivedCategory.Plus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)

end AlgebraicGeometry
