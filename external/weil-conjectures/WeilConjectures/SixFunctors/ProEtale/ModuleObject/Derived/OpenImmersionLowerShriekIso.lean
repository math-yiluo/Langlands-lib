/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence

/-!
# The lower shriek along an open immersion

Let `j : U ⟶ X` be a morphism of separated `k`-schemes of finite type whose underlying morphism
of schemes is an open immersion. On bounded constructible `ℚ̄_ℓ`-complexes, the lower shriek
`Rj_!`, defined through the compactification of `j` chosen by Nagata's theorem, is the extension by
zero `j_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl`).
The exceptional inverse image along `j` is treated in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- The identification of `X` with the middle object of the compactification
`U ⟶[j] X ⟶[𝟙] X` of an open immersion `j`. -/
noncomputable def openImmersionCompactificationHom :
    X ⟶ (Compactification.ofIsOpenImmersion j.left).overObj :=
  Over.homMk (𝟙 X.left) (by
    change 𝟙 X.left ≫ 𝟙 X.left ≫ X.hom = X.hom
    simp)

instance : IsIso (openImmersionCompactificationHom j) := by
  have : IsIso ((Over.forget _).map (openImmersionCompactificationHom j)) :=
    inferInstanceAs (IsIso (𝟙 X.left))
  exact isIso_of_reflects_iso _ (Over.forget _)

instance : IsProper (openImmersionCompactificationHom j).left :=
  inferInstanceAs (IsProper (𝟙 X.left))

omit [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma isPullback_openImmersionCompactificationHom :
    IsPullback (𝟙 U) j (Compactification.ofIsOpenImmersion j.left).overI
      (openImmersionCompactificationHom j) :=
  IsPullback.of_horiz_isIso ⟨by ext; simp [openImmersionCompactificationHom]; rfl⟩

omit [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] in
lemma openImmersionCompactificationHom_comp_overG :
    openImmersionCompactificationHom j ≫ (Compactification.ofIsOpenImmersion j.left).overG =
      𝟙 X := by
  ext
  simp [openImmersionCompactificationHom, Compactification.overG]
  rfl

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

/-- The lower shriek along an open immersion is the extension by zero, `Rj_! ≅ j_!`, on bounded
constructible `ℚ̄_ℓ`-complexes: by independence of the compactification
(`boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`), `Rj_!` is `j_! ⋙ R(𝟙 X)_*`
for the trivial compactification `U ⟶[j] X ⟶[𝟙] X`
(`AlgebraicGeometry.Compactification.ofIsOpenImmersion`), and `R(𝟙 X)_* ≅ 𝟭`. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl :
    boundedConstructibleLowerShriek ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ℓ
      (compactificationOverField j) (.ofIsOpenImmersion j.left) ≪≫
    Functor.isoWhiskerLeft (boundedConstructibleOpenImmersionLowerShriek _ ℓ j)
      (boundedConstructibleLowerStarId ℓ X) ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.ProEtale.CondensedRing
