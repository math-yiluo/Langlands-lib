/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage

/-!

# The closed complement of an open immersion over a base, and fully faithful extension by zero

For an open immersion `j : X ⟶ Z` of `S`-schemes, the closed complement of `j` as a morphism of
`Over S` (`overClosedComplement`) and the base change of a morphism of `S`-schemes
(`overPullbackObj`), with the finiteness instances they inherit. On bounded constructible complexes
of module objects over a commutative condensed ring `Λ`, the extension by zero `j_!` along an open
immersion is fully faithful (`fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek`), so the
unit of `j_! ⊣ Lj^*` is an isomorphism.

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-! ### The closed complement and base change in the category over a scheme -/

section Over

variable {S : Scheme.{u}}

/-- The closed complement of an open immersion `j : X ⟶ Z` of `S`-schemes, as an object of
`Over S`. -/
noncomputable def overClosedComplementObj {X Z : Over S} (j : X ⟶ Z)
    [IsOpenImmersion j.left] : Over S :=
  Over.mk (j.left.closedComplement ≫ Z.hom)

/-- The closed immersion of the closed complement of an open immersion `j : X ⟶ Z` of
`S`-schemes, as a morphism of `Over S`. -/
noncomputable def overClosedComplement {X Z : Over S} (j : X ⟶ Z)
    [IsOpenImmersion j.left] : (overClosedComplementObj j) ⟶ Z :=
  Over.homMk j.left.closedComplement rfl

section ClosedComplement

variable {X Z : Over S} (j : X ⟶ Z) [IsOpenImmersion j.left]

/-- The underlying morphism of schemes of `overClosedComplement j` is the closed complement of
`j`. -/
@[simp] lemma overClosedComplement_left :
    (overClosedComplement j).left = j.left.closedComplement := rfl

/-- The closed complement of an open immersion is a closed immersion. -/
instance : IsClosedImmersion (overClosedComplement j).left :=
  inferInstanceAs (IsClosedImmersion j.left.closedComplement)

/-- The closed complement of an `S`-scheme locally of finite type is locally of finite type. -/
instance [LocallyOfFiniteType Z.hom] : LocallyOfFiniteType (overClosedComplementObj j).hom :=
  inferInstanceAs (LocallyOfFiniteType (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of a quasi-compact `S`-scheme is quasi-compact. -/
instance [QuasiCompact Z.hom] : QuasiCompact (overClosedComplementObj j).hom :=
  inferInstanceAs (QuasiCompact (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of a separated `S`-scheme is separated. -/
instance [IsSeparated Z.hom] : IsSeparated (overClosedComplementObj j).hom :=
  inferInstanceAs (IsSeparated (j.left.closedComplement ≫ Z.hom))

/-- The closed complement of `j` is supported on the complement of the range of `j`. -/
lemma range_overClosedComplement :
    Set.range (overClosedComplement j).left.base = (Set.range j.left.base)ᶜ :=
  j.left.range_closedComplement

/-- The ranges of the closed complement of `j` and of `j` are complementary. -/
lemma isCompl_range_overClosedComplement :
    IsCompl (Set.range (overClosedComplement j).left.base) (Set.range j.left.base) := by
  rw [range_overClosedComplement]
  exact isCompl_compl.symm

end ClosedComplement

/-- The fibre product `Y ×_Z W` of morphisms `f : Y ⟶ Z` and `g : W ⟶ Z` of `S`-schemes, as an
object of `Over S` through the second projection. -/
noncomputable def overPullbackObj {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) : Over S :=
  Over.mk (pullback.snd f.left g.left ≫ W.hom)

/-- The first projection `Y ×_Z W ⟶ Y`, as a morphism of `Over S`. -/
noncomputable def overPullbackFst {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) :
    overPullbackObj f g ⟶ Y :=
  Over.homMk (pullback.fst f.left g.left) (by
    simp only [overPullbackObj, Over.mk_hom]
    rw [← Over.w f, pullback.condition_assoc, Over.w g])

/-- The second projection `Y ×_Z W ⟶ W`, as a morphism of `Over S`. -/
noncomputable def overPullbackSnd {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z) :
    overPullbackObj f g ⟶ W :=
  Over.homMk (pullback.snd f.left g.left) rfl

section Pullback

variable {Y Z W : Over S} (f : Y ⟶ Z) (g : W ⟶ Z)

/-- The underlying morphism of `overPullbackFst f g` is the first projection. -/
@[simp] lemma overPullbackFst_left : (overPullbackFst f g).left = pullback.fst f.left g.left :=
  rfl

/-- The underlying morphism of `overPullbackSnd f g` is the second projection. -/
@[simp] lemma overPullbackSnd_left : (overPullbackSnd f g).left = pullback.snd f.left g.left :=
  rfl

/-- The square of the fibre product in `Over S` is cartesian. -/
lemma isPullback_overPullbackFst_overPullbackSnd :
    IsPullback (overPullbackFst f g) (overPullbackSnd f g) f g :=
  IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext pullback.condition)
    (IsPullback.of_hasPullback f.left g.left)

/-- The base change of a proper morphism to an `S`-scheme locally of finite type is locally of
finite type over `S`. -/
instance [IsProper f.left] [LocallyOfFiniteType W.hom] :
    LocallyOfFiniteType (overPullbackObj f g).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left g.left ≫ W.hom))

/-- The base change of a proper morphism to a quasi-compact `S`-scheme is quasi-compact over
`S`. -/
instance [IsProper f.left] [QuasiCompact W.hom] : QuasiCompact (overPullbackObj f g).hom :=
  inferInstanceAs (QuasiCompact (pullback.snd f.left g.left ≫ W.hom))

/-- The base change of a proper morphism to a separated `S`-scheme is separated over `S`. -/
instance [IsProper f.left] [IsSeparated W.hom] : IsSeparated (overPullbackObj f g).hom :=
  inferInstanceAs (IsSeparated (pullback.snd f.left g.left ≫ W.hom))

end Pullback

/-- In a commutative square of `S`-schemes
```
X' --i'--> Z'
|p         |p'
v          v
X  --j---> Z
```
with `j` an open immersion, the base change of the closed complement of `j` along `p'` misses
the range of `i'`. -/
lemma disjoint_range_overPullbackFst_overClosedComplement {X Z X' Z' : Over S} {p : X' ⟶ X}
    {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z} [IsOpenImmersion j.left] (sq : CommSq p i' j p') :
    Disjoint (Set.range i'.left.base)
      (Set.range (overPullbackFst p' (overClosedComplement j)).left.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have h₁ := congrArg (fun φ : X' ⟶ Z ↦ φ.left x) sq.w
  have h₂ := congrArg (fun φ ↦ φ y) (pullback.condition (f := p'.left)
    (g := (overClosedComplement j).left))
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h₁ h₂
  rw [overPullbackFst_left] at hy
  exact (isCompl_range_overClosedComplement j).disjoint.ne_of_mem ⟨_, rfl⟩ ⟨_, rfl⟩
    (h₁.trans ((congrArg p'.left hy).symm.trans h₂)).symm

end Over

namespace ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

include ℓ k

/-! ### The extension by zero is fully faithful -/

section FullyFaithful

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The extension by zero `j_!` along an open immersion is fully faithful on bounded
constructible complexes: so is the levelwise `D((j)_!open⟦Λ⟧)` on the ambient derived
categories, the unit of `D(j_!) ⊣ D(j^*)` being an isomorphism. -/
noncomputable def fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).FullyFaithful :=
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  Functor.FullyFaithful.ofCompFaithful (G := (boundedConstructible _).ι)
    (((ObjectProperty.fullyFaithfulι _).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j.left).fullyFaithfulLOfIsIsoUnit).ofIso
        (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ j).symm)

/-- The unit `K ⟶ Lj^* j_! K` of the adjunction `j_! ⊣ Lj^*` on bounded constructible complexes
is an isomorphism, `j_!` being fully faithful. -/
instance isIso_boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j).unit :=
  have := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek Λ ℓ j).full
  have := (fullyFaithfulBoundedConstructibleOpenImmersionLowerShriek Λ ℓ j).faithful
  inferInstance

end FullyFaithful

end ProEtale.CondensedRing

end AlgebraicGeometry
