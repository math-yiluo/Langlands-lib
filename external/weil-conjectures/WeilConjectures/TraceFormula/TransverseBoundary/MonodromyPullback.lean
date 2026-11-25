/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverPullback
public import WeilConjectures.TraceFormula.TransverseBoundary.Basic

/-!
# Pullback of sheaves with finite `ℓ`-group monodromy

A sheaf of `Λ`-modules trivialized by a Galois cover `P ⟶ V` with group a finite `ℓ`-group
(`AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy`) pulls back along any `f : W ⟶ V` to a sheaf
trivialized by the base change `P ×_V W ⟶ W`, a Galois cover with the same group; the same holds
for bounded complexes with such cohomology
(`AlgebraicGeometry.Etale.IsBoundedFiniteEllGroupMonodromy`),
the pullback being exact
(blueprint `lemma-cohomology-near-two-transverse-divisors--1`).

## Main statements

- `AlgebraicGeometry.Etale.HasFiniteEllGroupMonodromy.upperStar`
- `AlgebraicGeometry.Etale.IsBoundedFiniteEllGroupMonodromy.mapDerivedCategoryUpperStar`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {ℓ : ℕ} {Λ : Type (u + 1)} [CommRing Λ] {W V : Scheme.{u}} (f : W ⟶ V)

/-- Having finite `ℓ`-group monodromy is invariant under isomorphism of sheaves. -/
theorem HasFiniteEllGroupMonodromy.of_iso {V : Scheme.{u}}
    {F F' : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : HasFiniteEllGroupMonodromy ℓ F)
    (e : F ≅ F') : HasFiniteEllGroupMonodromy ℓ F' := by
  obtain ⟨G, _, _, hG, c, M, hM, ⟨φ⟩⟩ := hF
  exact ⟨G, _, _, hG, c, M, hM, ⟨((c.π)^*[ModuleCat.{u + 1} Λ]).mapIso e.symm ≪≫ φ⟩⟩

/-- The pullback of a sheaf with finite `ℓ`-group monodromy along any morphism has finite
`ℓ`-group monodromy: it is trivialized by the base change of the trivializing Galois cover. -/
theorem HasFiniteEllGroupMonodromy.upperStar
    {F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (hF : HasFiniteEllGroupMonodromy ℓ F) :
    HasFiniteEllGroupMonodromy ℓ ((f)^*[ModuleCat.{u + 1} Λ].obj F) := by
  obtain ⟨G, _, _, hG, c, M, hM, ⟨φ⟩⟩ := hF
  refine ⟨G, _, _, hG, c.pullback f, M, hM, ⟨?_⟩⟩
  exact ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd c.π f) f).app F).symm ≪≫
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.fst c.π f) c.π _
      pullback.condition.symm).app F ≪≫
    ((pullback.fst c.π f)^*[ModuleCat.{u + 1} Λ]).mapIso φ ≪≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (pullback.fst c.π f)).app M

/-- The pullback of a bounded complex whose cohomology sheaves have finite `ℓ`-group monodromy
again has these properties, the pullback being exact. -/
theorem IsBoundedFiniteEllGroupMonodromy.mapDerivedCategoryUpperStar
    {E : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE : IsBoundedFiniteEllGroupMonodromy ℓ E) :
    IsBoundedFiniteEllGroupMonodromy ℓ ((D((f)^*[ModuleCat.{u + 1} Λ])).obj E) := by
  obtain ⟨⟨a, b, ha, hb⟩, hE⟩ := hE
  refine ⟨⟨a, b, ((f)^*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj E a,
    ((f)^*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj E b⟩, fun n ↦ ?_⟩
  exact ((hE n).upperStar f).of_iso
    ((((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n).app E)

end AlgebraicGeometry.Etale
