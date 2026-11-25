/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapComp
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Algebra.AddConjugate

/-!
# Pullback maps on étale cohomology up to isomorphism

We record when two pullback maps on étale cohomology are conjugate
(`Function.AddConjugate`), i.e. agree up to isomorphisms of their sources and targets:

* replacing the coefficient sheaf by an isomorphic one;
* for a commutative square `r' ≫ i = j ≫ r` of schemes whose sides `r` and `r'` are universal
  homeomorphisms, the pullback maps along `i` and along `j` are conjugate, since pullback along a
  universal homeomorphism is bijective on cohomology (topological invariance).

## Main statements

- `AlgebraicGeometry.Etale.addConjugate_cohomologyMap_of_iso`
- `AlgebraicGeometry.Etale.addConjugate_cohomologyMap_of_comm`
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

/-- Pre- and postcomposition with the classes of isomorphisms, as an additive equivalence of
`Ext`-groups. -/
noncomputable def extMk₀CompCompMk₀AddEquiv {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A A' B B' : C} (e : A' ⟶ A) [IsIso e] (e' : B ⟶ B') [IsIso e'] (n : ℕ) :
    Ext A B n ≃+ Ext A' B' n :=
  { Equiv.ofBijective _ (bijective_mk₀_comp_comp_mk₀ e e' n) with
    map_add' a b := by
      change (Ext.mk₀ e).comp ((a + b).comp (Ext.mk₀ e') (add_zero n)) (zero_add n) =
        (Ext.mk₀ e).comp (a.comp (Ext.mk₀ e') (add_zero n)) (zero_add n) +
        (Ext.mk₀ e).comp (b.comp (Ext.mk₀ e') (add_zero n)) (zero_add n)
      rw [Ext.add_comp, Ext.comp_add] }

variable {X Y : Scheme.{u}}

/-- The pullback map along `j` does not depend, up to conjugacy, on the coefficient sheaf within
its isomorphism class. -/
theorem addConjugate_cohomologyMap_of_iso (j : X ⟶ Y)
    {G G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : G ≅ G') (n : ℕ) :
    Function.AddConjugate (cohomologyMap j G n) (cohomologyMap j G' n) :=
  ⟨AddEquiv.ofBijective _ (Sheaf.H.map_bijective_of_iso e n),
    AddEquiv.ofBijective _
      (Sheaf.H.map_bijective_of_iso (((j)^*[AddCommGrpCat.{u + 1}]).mapIso e) n),
    fun x ↦ (cohomologyMap_map j n e.hom x).symm⟩

/-- **Pullback maps across universal homeomorphisms.** For a commutative square
`r' ≫ i = j ≫ r` of schemes in which `r` and `r'` are universal homeomorphisms, the pullback map
on étale cohomology along `i` is conjugate to the pullback map along `j` of the pulled-back
sheaf. -/
theorem addConjugate_cohomologyMap_of_comm {P₀ P₁ P₂ P₃ : Scheme.{u}} (i : P₁ ⟶ P₀)
    (r : P₂ ⟶ P₀) (j : P₃ ⟶ P₂) (r' : P₃ ⟶ P₁) (h : r' ≫ i = j ≫ r)
    [IsUniversalHomeomorphism r] [IsUniversalHomeomorphism r']
    (G : Sheaf P₀.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.AddConjugate (cohomologyMap i G n)
      (cohomologyMap j (((r)^*[AddCommGrpCat.{u + 1}]).obj G) n) := by
  let α := extMk₀CompCompMk₀AddEquiv (cohomologyMapCompIso r' i _ rfl).hom
    ((upperStarComp AddCommGrpCat.{u + 1} r' i (r' ≫ i) rfl).hom.app G) n
  let β := extMk₀CompCompMk₀AddEquiv (cohomologyMapCompIso j r _ h.symm).hom
    ((upperStarComp AddCommGrpCat.{u + 1} j r (r' ≫ i) h).hom.app G) n
  have hα : ∀ x, cohomologyMap r' _ n (cohomologyMap i G n x) =
      α (cohomologyMap (r' ≫ i) G n x) :=
    fun x ↦ cohomologyMap_cohomologyMap_of_comp_eq r' i _ rfl G x
  have hβ : ∀ x, cohomologyMap j _ n (cohomologyMap r G n x) =
      β (cohomologyMap (r' ≫ i) G n x) :=
    fun x ↦ cohomologyMap_cohomologyMap_of_comp_eq j r _ h.symm G x
  let e₁ := AddEquiv.ofBijective _ (cohomologyMap_bijective r G n)
  let e₂ := (AddEquiv.ofBijective _ (cohomologyMap_bijective r'
    (((i)^*[AddCommGrpCat.{u + 1}]).obj G) n)).trans (α.symm.trans β)
  refine ⟨e₁, e₂, fun x ↦ ?_⟩
  change β (α.symm (cohomologyMap r' _ n (cohomologyMap i G n x))) =
    cohomologyMap j _ n (cohomologyMap r G n x)
  rw [hα, hβ, AddEquiv.symm_apply_apply]

end AlgebraicGeometry.Etale
